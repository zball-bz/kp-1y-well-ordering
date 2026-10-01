#!/usr/bin/env python3
"""Inspect kernel dependencies of every declaration explicitly listed in Audit.lean.

Reads existing module artifacts; does not run lake build or rebuild dependencies.
Run check-module.sh KP1Y.lean --emit after changing the root imports first.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parent
import shutil
_bundled = root.parent / ".tools/lean-4.33.1-linux/bin/lean"
lean = Path(os.environ["KP_LEAN"]) if os.environ.get("KP_LEAN") else (_bundled if _bundled.exists() else Path(shutil.which("lean") or "lean"))
audit_env = dict(os.environ)
audit_env["LEAN_PATH"] = ":".join(str(p) for p in [
    root / "third_party/YesMetaZFC/.lake/build/lib/lean",
    root / ".lake/build/lib/lean",
])
audit_env["LEAN_NUM_THREADS"] = "4"
run = subprocess.run([str(lean), "-DautoImplicit=false", "Audit.lean"], cwd=root, env=audit_env,
                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
(root / "audit.log").write_text(run.stdout)
if run.returncode:
    print(run.stdout, file=sys.stderr)
    sys.exit(run.returncode)
expected = re.findall(r"^#print axioms (\S+)$", (root / "Audit.lean").read_text(), re.M)
results = {}
pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
for name, dependencies in re.findall(pattern, run.stdout):
    if name in results:
        sys.exit(f"Duplicate audit result: {name}")
    results[name] = [entry.strip() for entry in dependencies.split(",") if entry.strip()]
if len(expected) != len(set(expected)) or set(expected) != set(results):
    sys.exit(f"Audit declaration mismatch: missing={set(expected)-set(results)}, extra={set(results)-set(expected)}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
failures = {name: sorted(set(deps)-allowed) for name, deps in results.items() if set(deps)-allowed}
(root / "audit-results.json").write_text(json.dumps(results, ensure_ascii=False, indent=2) + "\n")
if failures:
    print(json.dumps(failures, ensure_ascii=False, indent=2), file=sys.stderr)
    sys.exit(1)
print(f"PASS: {len(results)} declarations; only propext, Classical.choice, Quot.sound.")
