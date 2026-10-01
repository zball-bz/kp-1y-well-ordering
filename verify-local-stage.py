#!/usr/bin/env python3
"""Stage verification of local Lean sources with strict options; reuses dependency artifacts.

No lake build and no third-party rebuild. Successful unchanged fingerprints may be
reused on a resumed invocation; source and local dependency changes invalidate them.
"""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', action='append', default=[],
                    help='Check only the local import closure of a frozen module (for concurrent work).')
args = parser.parse_args()
logdir = root / "strict-stage"
logdir.mkdir(exist_ok=True)
report = logdir / "results.json"
prior = json.loads(report.read_text()) if report.exists() else {}
paths = {"KP1Y." + p.stem: p for p in (root / "KP1Y").glob("*.lean")}
paths["KP1Y"] = root / "KP1Y.lean"
deps = {}
for name, path in paths.items():
    imports = re.findall(r"^import\s+([A-Za-z0-9_.]+)", path.read_text(), re.M)
    deps[name] = {item for item in imports if item in paths}

if args.root:
    selected = set()
    def include(name):
        if name not in paths:
            parser.error(f'Unknown local root: {name}')
        if name in selected:
            return
        selected.add(name)
        for dependency in deps[name]:
            include(dependency)
    for name in args.root:
        include(name)
    paths = {name: path for name, path in paths.items() if name in selected}
    deps = {name: local_deps for name, local_deps in deps.items() if name in selected}

results, fingerprints, pending, running = {}, {}, set(paths), {}
failed = set()
reused = 0

def check(name, fingerprint):
    path = paths[name]
    run = subprocess.run([str(root / "check-module.sh"), str(path.relative_to(root)), "--emit"],
                         cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (logdir / (name + ".log")).write_text(run.stdout)
    return {"fingerprint": fingerprint, "exit_code": run.returncode,
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}

with ThreadPoolExecutor(max_workers=2) as pool:
    while pending or running:
        ready = sorted(n for n in pending if deps[n] <= results.keys() and not (deps[n] & failed))
        for name in ready:
            if len(running) >= 2:
                break
            payload = b"strict-autoImplicit-false-v1\0" + paths[name].read_bytes()
            payload += "".join(fingerprints[d] for d in sorted(deps[name])).encode()
            fingerprint = hashlib.sha256(payload).hexdigest()
            fingerprints[name] = fingerprint
            pending.remove(name)
            olean = root / ".lake/build/lib/lean" / (name.replace(".", "/") + ".olean")
            if prior.get(name, {}).get("fingerprint") == fingerprint and prior[name].get("exit_code") == 0 and olean.exists():
                results[name] = prior[name]
                reused += 1
            else:
                running[pool.submit(check, name, fingerprint)] = name
        if not running:
            if pending and not ready:
                break
            continue
        done, _ = wait(running, return_when=FIRST_COMPLETED)
        for future in done:
            name = running.pop(future)
            result = future.result()
            results[name] = result
            if result["exit_code"]:
                failed.add(name)
                print(f"FAIL {name}", flush=True)
                print((logdir / (name + ".log")).read_text(), flush=True)
            elif len(results) % 20 == 0:
                print(f"Checked {len(results)}/{len(paths)} local modules", flush=True)
        report.write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n")

report.write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n")
if failed or pending:
    print(f"Failed: {sorted(failed)}; blocked local modules: {sorted(pending)}")
    sys.exit(1)
print(f"PASS: {len(results)} local modules validated "
      f"({len(results) - reused} checked, {reused} cached), autoImplicit=false; third-party artifacts reused.")
