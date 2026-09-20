"""Trusted verifier for captured multi-file research; never uses worker object files."""
from pathlib import Path
import hashlib, json, re, uuid
from runtime import Controller, lean_code_without_comments, parse_axioms, atomic_json, git
from resources import slot


def verify_snapshot(queue, job, targets, workspace):
    cfg = queue.store.get_project(job['project_id'])
    controller = Controller(queue.store, queue.state_root, job['project_id'])
    root, objects = workspace/'source', workspace/'objects'
    files = [x for x in job['manifest']['files'] if x['kind'] == 'source']
    modules = {x['path'][:-5].replace('/', '.'): x for x in files}
    owned = set(modules)
    imports, local_holes = {}, []
    for name, entry in modules.items():
        code = lean_code_without_comments((root/entry['path']).read_text())
        if re.search(r'\b(axiom|unsafe|native_decide|ofReduceBool|implemented_by)\b|skipKernelTC', code):
            raise ValueError('unsupported proof escape in captured source: '+entry['path'])
        if re.search(r'\b(sorry|admit)\b', code):
            local_holes.append(entry['path'])
        lines = re.findall(r'(?m)^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)', code)
        imports[name] = sorted({v for line in lines for v in line.split() if v in owned})
    order, visiting, visited = [], set(), set()
    def visit(name):
        if name in visiting:
            raise ValueError('cycle among captured source modules')
        if name in visited:
            return
        visiting.add(name)
        for parent in imports[name]:
            visit(parent)
        visiting.remove(name); visited.add(name); order.append(name)
    for name in sorted(modules):
        visit(name)
    target_modules = sorted({x['path'][:-5].replace('/', '.') for x in targets})
    if not set(target_modules) <= owned:
        raise ValueError('trusted target is not one of the frozen sources')
    with slot(queue.state_root, 'verifier', int(cfg.get('verifier_slots', 2)), timeout=600):
        for name in order:
            entry = modules[name]
            controller._compile(root/entry['path'], objects, entry['path'])
        relative = 'ResearchAudit_' + uuid.uuid4().hex + '.lean'
        audit = workspace/relative
        text = '\n'.join('import '+name for name in target_modules) + '\n'
        text += '\n'.join('#print axioms '+x['name'] for x in targets) + '\n'
        audit.write_text(text)
        controller._compile(audit, objects, relative)
        output = (objects/(Path(relative).stem+'.log')).read_text()
        axioms = {x['name']: parse_axioms(output, x['name']) for x in targets}
    evidence = {'compile_passed': True, 'transitive_axioms_checked': True,
        'target_axioms': axioms, 'compiled_sources': sorted(x['path'] for x in files),
        'compiled_modules': order, 'local_proof_holes': sorted(local_holes),
        'baseline_commit': git(controller.repo, 'rev-parse', cfg['integration_branch']),
        'audit_output_sha256': hashlib.sha256(output.encode()).hexdigest()}
    output_dir = queue.state_root/'research'/'audits'/job['job_id']
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir/(Path(relative).stem+'.log')).write_text(output)
    atomic_json(output_dir/(Path(relative).stem+'.json'), evidence)
    return evidence
