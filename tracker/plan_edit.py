#!/usr/bin/env python3
"""Coordinator helper: apply small edits to plan.py and rewrite it.
usage: plan_edit.py '<python statements using T (task dict by id), META, WORK, WAVES>'"""
import importlib.util, pprint, sys
path = __file__.rsplit('/', 1)[0] + '/plan.py'
spec = importlib.util.spec_from_file_location('plan', path); plan = importlib.util.module_from_spec(spec); spec.loader.exec_module(plan)
doc = open(path).read().split('\n', 1)[0]
T = {t['id']: t for t in plan.TASKS}
exec(sys.argv[1], dict(T=T, META=plan.META, WORK=plan.WORK, WAVES=plan.WAVES))
with open(path, 'w') as f:
    f.write(doc + '\n\n')
    for name in ('TASKS', 'META', 'WORK', 'WAVES'):
        f.write(f'{name} = ' + pprint.pformat(getattr(plan, name), width=120, sort_dicts=False) + '\n\n')
