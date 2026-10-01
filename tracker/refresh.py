#!/usr/bin/env python3
"""Refresh the read-only tracker snapshot. Default path never invokes Lean.

--audit runs the existing audit.py against built artifacts (no dependency build),
then records hashes tying that successful audit to its inputs.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone
from plan import TASKS, WAVES, META, WORK

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None

def read_json(p, default):
    return json.loads(p.read_text()) if p.exists() else default

def iso(ts):
    return datetime.fromtimestamp(ts, timezone.utc).isoformat(timespec='seconds')

def source_snapshot():
    paths = {'KP1Y.' + p.stem: p for p in sorted((ROOT / 'KP1Y').glob('*.lean'))}
    paths['KP1Y'] = ROOT / 'KP1Y.lean'
    texts = {n: p.read_text() for n, p in paths.items()}
    imports = {n: re.findall(r'^import\s+([A-Za-z0-9_.]+)', t, re.M) for n, t in texts.items()}
    deps = {n: sorted(d for d in ds if d in paths) for n, ds in imports.items()}
    stage = read_json(ROOT / 'strict-stage/results.json', {})
    fps, visiting = {}, set()

    def fingerprint(n):
        if n in fps:
            return fps[n]
        if n in visiting:
            raise ValueError(f'Import cycle: {n}')
        visiting.add(n)
        payload = b'strict-autoImplicit-false-v1\0' + paths[n].read_bytes()
        payload += ''.join(fingerprint(d) for d in deps[n]).encode()
        fps[n] = hashlib.sha256(payload).hexdigest()
        visiting.remove(n)
        return fps[n]

    modules = []
    for n, p in paths.items():
        fp = fingerprint(n)
        artifact = ROOT / '.lake/build/lib/lean' / (n.replace('.', '/') + '.olean')
        row = stage.get(n, {})
        fresh = row.get('fingerprint') == fp and row.get('exit_code') == 0 and artifact.exists()
        decls = [{'name': m.group(1), 'line': texts[n][:m.start()].count('\n') + 1}
                 for m in re.finditer(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|structure|inductive|abbrev)\s+([^\s:{(]+)', texts[n], re.M)]
        modules.append(dict(id=n, name=p.stem, path=str(p.relative_to(ROOT)),
            href='../' + str(p.relative_to(ROOT)), imports=deps[n],
            external_imports=[d for d in imports[n] if d not in paths],
            lines=len(texts[n].splitlines()), checked=fresh, sha256=sha(p),
            fingerprint=fp, declarations=decls, tasks=[]))
    return modules, fps, stage

def audit_inputs(root_fp):
    return dict(audit_source=sha(ROOT / 'Audit.lean'), report=sha(ROOT / 'audit-results.json'),
        root_fingerprint=root_fp, root_artifact=sha(ROOT / '.lake/build/lib/lean/KP1Y.olean'),
        lean_toolchain=sha(ROOT / 'lean-toolchain'), provenance=sha(ROOT / 'third_party-provenance.json'))

def audit_summary(fps):
    actual = read_json(ROOT / 'audit-results.json', {})
    expected = re.findall(r'^#print axioms (\S+)$', (ROOT / 'Audit.lean').read_text(), re.M)
    valid = len(expected) == len(set(expected)) and set(expected) == set(actual)
    valid = valid and all(set(v) <= ALLOWED for v in actual.values())
    receipt = read_json(HERE / 'audit-receipt.json', {})
    fresh = valid and receipt.get('inputs') == audit_inputs(fps['KP1Y'])
    return dict(count=len(actual), expected=len(expected), valid=valid, fresh=fresh,
        at=receipt.get('at'), receipt='../tracker/audit-receipt.json',
        allowed=sorted(ALLOWED), scope=len(receipt.get('modules', []))), actual

def checkpoint_evidence(stage, audit):
    """Preserve unaffected evidence from the last audited root snapshot.

    The old root fingerprint must still match the stage manifest, and all
    non-source audit inputs must match. A task additionally checks each module's
    current dependency fingerprint; editing Mountain need not invalidate F01.
    """
    receipt=read_json(HERE/'audit-receipt.json', {})
    old=receipt.get('inputs', {})
    current=audit_inputs(old.get('root_fingerprint'))
    valid=(audit['valid'] and old == current and
           stage.get('KP1Y', {}).get('fingerprint') == old.get('root_fingerprint'))
    return set(receipt.get('modules', [])) if valid else set()

def record_current_audit():
    """Call only immediately after observing a successful audit.py invocation."""
    modules, fps, _ = source_snapshot()
    summary, _ = audit_summary(fps)
    by_id = {m['id']: m for m in modules}
    closure = set()
    def include(name):
        if name in closure:
            return
        closure.add(name)
        for dependency in by_id[name]['imports']:
            include(dependency)
    include('KP1Y')
    # Audit.lean is deliberately maintained as a single-root audit by the coordinator.
    imports = re.findall(r'^import\s+([A-Za-z0-9_.]+)', (ROOT/'Audit.lean').read_text(), re.M)
    if imports != ['KP1Y']:
        raise ValueError('Audit imports changed; extend the receipt scope before recording it.')
    if not summary['valid'] or not all(by_id[n]['checked'] for n in closure):
        raise ValueError('Current source/stage/audit mismatch; cannot record receipt.')
    stamp = dict(at=iso((ROOT / 'audit-results.json').stat().st_mtime),
                 method='audit.py: existing artifacts, autoImplicit=false, no dependency build',
                 inputs=audit_inputs(fps['KP1Y']), modules=sorted(closure))
    (HERE / 'audit-receipt.json').write_text(json.dumps(stamp, indent=2) + '\n')

def validate_plan(tasks):
    by_id = {t['id']: t for t in tasks}
    assert len(by_id) == len(tasks), 'Duplicate task IDs'
    visited, stack = set(), set()
    owners = {}
    def visit(n):
        if n in visited:
            return
        assert n not in stack, f'Task dependency cycle: {n}'
        assert n in by_id, f'Unknown task: {n}'
        stack.add(n)
        for d in by_id[n]['deps']:
            visit(d)
        stack.remove(n)
        visited.add(n)
    for t in tasks:
        visit(t['id'])
        assert not t['declared_done'] or t['evidence'], f'Completed task without evidence: {t["id"]}'
        for f in t['files']:
            assert f not in owners, f'File ownership collision: {f}'
            owners[f] = t['id']
    completed = {t['id'] for t in tasks if t['declared_done'] or t.get('delivered')}
    baseline = set(completed)
    scheduled = set()
    for wave in WAVES:
        before = set(completed)
        for n in wave.get('coordinator_tasks', []):
            if n in baseline:
                continue
            assert set(by_id[n]['deps']) <= before, f'Coordinator dependency violation: {n}'
            before.add(n)
            scheduled.add(n)
        ends = set()
        for lane in wave['lanes']:
            available = set(before)
            for n in lane:
                if n in baseline:
                    available.add(n)
                    continue
                assert n not in scheduled, f'Duplicate scheduling: {n}'
                assert set(by_id[n]['deps']) <= available, f'Wave dependency violation: {n}'
                available.add(n)
                ends.add(n)
                scheduled.add(n)
        completed |= before | ends
    assert scheduled == set(by_id)-baseline, 'Unscheduled task'

def prompt_for(t):
    verification = ('由协调者统一运行严格阶段检查与 audit.py。' if t['id'] == 'Q02' else
        '每个稳定模块只做单文件增量检查：./check-module.sh KP1Y/YourModule.lean --emit。不要运行 lake build；不要编译别人的模块。')
    return f'''任务 {t['id']}：{t['title']}
工程：{ROOT}
先读 tracker/README.md、tracker/INTERFACES.md 及前置任务交接。主目标是对象 KPω 内的完整推导。
前置任务：{', '.join(t['deps']) or '无'}。协调者确认前置通过后才开始依赖工作。
交付：{t['result']}
输入：{t['inputs']}
仅负责：{', '.join(t['files']) or '只读审查，不修改证明源码'}。
不要复制当前活跃worker的任务；先查tracker/CURRENT.md及实际agent状态。模式由当前会话设置继承，本任务不自行更改。
验收：\n''' + '\n'.join(f'- {a}' for a in t['accept']) + f'''
注意：{t['risk'] or '所有内部长度和 N 必须量化模型内部 ω。'}
不加入 sorry、admit、新 Lean 公理或额外对象公理；不假设 ω 标准或宿主 membership 良基。
{verification}
共享 KP1Y.lean、Audit.lean、基础接口和全局清单仅由协调者修改（Q02 为协调者任务）。
若需改越界接口，提交具体 theorem 类型与理由给协调者，继续可独立完成部分。
交接需给出：新 theorem 完整类型、负责文件、单模块检查日志、待审计声明列表、未解除的假设和下一步依赖。
不要把条件定理或宿主 Nat 证明报告为对象 KPω 主定理完成。'''

def build_data():
    tasks = copy.deepcopy(TASKS)
    validate_plan(tasks)
    modules, fps, stage = source_snapshot()
    by_mod = {m['id']: m for m in modules}
    audit, declarations = audit_summary(fps)
    checkpoint = checkpoint_evidence(stage, audit)
    deliveries = read_json(HERE/'deliveries.json', {})
    for t in tasks:
        t['links'] = []
        sources_fresh = True
        scoped = True
        for e in t['evidence']:
            if '/' in e:
                p = (HERE / e).resolve()
                assert p.exists(), f'Missing evidence: {p}'
                t['links'].append(dict(label=p.name, href=e))
            else:
                n = 'KP1Y.' + e
                assert n in by_mod, f'Missing evidence module: {n}'
                m = by_mod[n]
                m['tasks'].append(t['id'])
                sources_fresh &= m['checked']
                scoped &= n in checkpoint
                t['links'].append(dict(label=e + '.lean', href=m['href'], module=n))
        for s in t['symbols']:
            assert s in declarations, f'Representative theorem absent from audit: {s}'
        if t['declared_done']:
            if t['id'] == 'V01':
                t['status'] = 'historical'
            else:
                t['status'] = 'verified' if sources_fresh and scoped else 'stale'
        elif t.get('delivered'):
            record=deliveries.get(t['id'], {})
            matches=bool(record)
            for n, r in record.get('modules', {}).items():
                m=by_mod.get(n, {})
                artifact=ROOT/'.lake/build/lib/lean'/(n.replace('.', '/')+'.olean')
                matches &= (m.get('fingerprint') == r.get('fingerprint') and
                            sha(artifact) == r.get('artifact') and
                            sha(ROOT/r['log']) == r.get('log_sha256'))
            matches &= set(record.get('modules', {})) == {'KP1Y.'+m for m in t['evidence']}
            t['status']='delivered' if matches else 'stale'
            t['delivery']=record
        else:
            t['status'] = 'planned'
        t['prompt'] = prompt_for(t)
    by_id = {t['id']: t for t in tasks}
    for t in tasks:
        t['unmet'] = [d for d in t['deps'] if by_id[d]['status'] not in ('verified','historical','delivered')]
        t['pending_integration'] = [d for d in t['deps'] if by_id[d]['status'] == 'delivered']
        t['dependents'] = [x['id'] for x in tasks if t['id'] in x['deps']]
        if t['status'] == 'planned':
            t['status'] = 'waiting' if t['unmet'] else 'ready'
    for t in tasks:
        t['work'] = WORK.get(t['id'])
        if t['work'] and t['work'].get('state') != 'queued' and not t['declared_done'] and not t.get('delivered'):
            t['status'] = 'working'
        t['dependency_state'] = 'waiting' if t['unmet'] else 'available'
    total = len(modules)
    log = (ROOT / 'latest-stage.log').read_text() if (ROOT / 'latest-stage.log').exists() else ''
    match = re.search(r'PASS: (\d+) local modules validated \((\d+) checked, (\d+) cached\)', log)
    stats = dict(modules=total-1, lines=sum(m['lines'] for m in modules if m['id'] != 'KP1Y'),
        strict_total=total, strict_fresh=sum(m['checked'] for m in modules),
        audit=audit, import_edges=sum(len(m['imports']) for m in modules),
        last_stage=dict(total=int(match[1]), checked=int(match[2]), cached=int(match[3])) if match else None,
        stage_at=iso((ROOT/'strict-stage/results.json').stat().st_mtime),
        verified_tasks=sum(t['status'] == 'verified' for t in tasks),
        delivered_tasks=sum(t['status'] == 'delivered' for t in tasks),
        remaining_tasks=sum(not t['declared_done'] and not t.get('delivered') and not t['optional'] for t in tasks),
        optional_tasks=sum(t['optional'] for t in tasks))
    return dict(meta=META, generated_at=iso(datetime.now().timestamp()), stats=stats,
                tasks=tasks, waves=WAVES, modules=modules)

def write_docs(data):
    docs = ['# 数学依赖与逐任务验收\n', META['statement'], '\n' + META['source_statement'],
            '\n此文件由 `plan.py` 生成；修改计划后运行 `python3 tracker/refresh.py`，不调用 Lean。',
            '\n依赖边表示所需输入或验收前置；实际 Lean import 另见看板。历史成果节点不代表主定理已经完成。\n',
            '```mermaid\nflowchart LR']
    for t in data['tasks']:
        docs.append(f'  {t["id"]}["{t["id"]} {t["title"]}"]')
        docs.extend(f'  {d} --> {t["id"]}' for d in t['deps'])
    for edge in META.get('optional_edges', []):
        docs.append(f'  {edge["source"]} -. "可选复用，不阻塞" .-> {edge["target"]}')
    docs.append('```\n')
    for t in data['tasks']:
        docs += [f'## {t["id"]} · {t["title"]}\n', t['result'],
            f'\n前置：{", ".join(t["deps"]) or "无"}。输入：{t["inputs"]}',
            f'\n负责文件：{", ".join(t["files"]) or "既有成果，只读"}。',
            f'\n快照状态：{t["status"]}；未就绪前置：{", ".join(t["unmet"]) or "无"}。', '\n验收：\n']
        docs.extend('- ' + a for a in t['accept'])
        if t['risk']:
            docs.append('\n注意：' + t['risk'])
        if t['links']:
            docs.append('\n证据：' + '、'.join(f'[{l["label"]}]({l["href"]})' for l in t['links']))
        docs.append('')
    (HERE/'DEPENDENCIES.md').write_text('\n'.join(docs))
    prompts = HERE/'prompts'
    prompts.mkdir(exist_ok=True)
    # Retired tasks must not remain available as apparently current instructions.
    valid_prompts={t['id']+'.md' for t in data['tasks'] if not t['declared_done'] and not t.get('delivered')}
    for p in prompts.glob('*.md'):
        if p.name not in valid_prompts:
            p.unlink()
    for t in data['tasks']:
        if not t['declared_done'] and not t.get('delivered'):
            (prompts/(t['id']+'.md')).write_text(t['prompt']+'\n')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit',action='store_true',help='Audit existing artifacts, then refresh; no dependency compilation.')
    args=parser.parse_args()
    if args.audit:
        subprocess.run([sys.executable, str(ROOT/'audit.py')],cwd=ROOT,check=True)
        record_current_audit()
    data=build_data()
    (HERE/'data.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
    encoded=json.dumps(data,ensure_ascii=False,separators=(',',':')).replace('<','\\u003c')
    template=(HERE/'template.html').read_text()
    assert template.count('/*__TRACKER_DATA__*/') == 1
    (HERE/'index.html').write_text(template.replace('/*__TRACKER_DATA__*/',encoded))
    write_docs(data)
    print(json.dumps(dict(modules=data['stats']['modules'],strict_fresh=data['stats']['strict_fresh'],
        audit_fresh=data['stats']['audit']['fresh'],audit=data['stats']['audit']['count'],
        tasks=len(data['tasks']),remaining=data['stats']['remaining_tasks']),ensure_ascii=False))

if __name__ == '__main__':
    main()
