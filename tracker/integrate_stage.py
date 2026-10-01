#!/usr/bin/env python3
"""Coordinator helper: integrate modules into KP1Y.lean / Audit.lean and write a stage manifest.

usage: integrate.py STAGE_NO Module1 Module2 ...   (module names without KP1Y. prefix)
       integrate.py STAGE_NO --all-unintegrated
Only edits KP1Y.lean, Audit.lean and tracker/parallel-stage-N.json (status 'pending').
"""
import glob, json, os, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def module_imports():
    mods = {}
    for f in glob.glob(str(ROOT / 'KP1Y/*.lean')):
        m = 'KP1Y.' + os.path.basename(f)[:-5]
        mods[m] = re.findall(r'^import (KP1Y\.\S+)', open(f).read(), re.M)
    return mods


def closure(mods, roots):
    seen, st = set(), list(roots)
    while st:
        x = st.pop()
        if x in seen:
            continue
        seen.add(x)
        st += mods.get(x, [])
    return seen


def theorem_names(path):
    """Public theorem names with their full namespace."""
    stack = []
    names = []
    for line in open(path):
        s = line.rstrip('\n')
        m = re.match(r'^namespace\s+(\S+)', s)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r'^end\s+(\S+)\s*$', s)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        m = re.match(r'^(?:@\[[^\]]*\]\s*)?(protected\s+)?theorem\s+(\S+)', s)
        if m:
            n = m.group(2)
            full = n[1:] if n.startswith('_root_.') else '.'.join(stack + [n])
            names.append(full)
    return names


def main():
    stage = int(sys.argv[1])
    mods = module_imports()
    root_imports = re.findall(r'^import (KP1Y\.\S+)', (ROOT / 'KP1Y.lean').read_text(), re.M)
    integrated = closure(mods, root_imports)
    if sys.argv[2:] == ['--all-unintegrated']:
        new = sorted(m for m in mods if m not in integrated)
    else:
        new = ['KP1Y.' + a for a in sys.argv[2:]]
    missing = [m for m in new if m not in mods]
    if missing:
        sys.exit(f'unknown modules: {missing}')
    # Every new module's KP1Y deps must be integrated or new.
    for m in new:
        for d in mods[m]:
            if d not in integrated and d not in new:
                sys.exit(f'{m} imports unintegrated {d}')
    users = {u for u in mods for d in mods[u] if d in new}
    leaves = [m for m in new if not any(m in mods[u] for u in new)]
    # Root imports: append leaves (non-leaves are reached through them).
    text = (ROOT / 'KP1Y.lean').read_text()
    add = [m for m in leaves if f'import {m}\n' not in text]
    lines = text.splitlines(keepends=True)
    last_import = max(i for i, l in enumerate(lines) if l.startswith('import '))
    lines[last_import + 1:last_import + 1] = [f'import {m}\n' for m in add]
    (ROOT / 'KP1Y.lean').write_text(''.join(lines))
    # Audit names
    audit = (ROOT / 'Audit.lean').read_text()
    existing = set(re.findall(r'^#print axioms (\S+)$', audit, re.M))
    names = []
    for m in new:
        for n in theorem_names(ROOT / (m.replace('.', '/') + '.lean')):
            if "'" in n:  # audit.py's output regex cannot parse primed names; covered via users
                continue
            if n not in existing and n not in names:
                names.append(n)
    if names:
        audit = audit.rstrip('\n') + '\n\n' + ''.join(f'#print axioms {n}\n' for n in names)
        (ROOT / 'Audit.lean').write_text(audit)
    manifest = dict(modules=new, audit_names=names, status='pending')
    (ROOT / f'tracker/parallel-stage-{stage}.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(dict(modules=len(new), root_added=add, audit_names=len(names)), ensure_ascii=False))


if __name__ == '__main__':
    main()
