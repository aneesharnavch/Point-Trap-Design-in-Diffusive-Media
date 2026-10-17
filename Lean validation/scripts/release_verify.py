#!/usr/bin/env python3
"""Verify the source release; optionally reproduce Lean checks with ordinary Lake.

Default mode checks recorded hashes, proof guards, namespace-aware inventory,
and the archived integrated axiom audit. It does NOT run Lean. `--lean` runs
new checks and writes a distinct reproduction report, never a historical record.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def theorem_names(source, path):
    """Handle one or successive fully qualified namespaces; reject ambiguity.

This release contains five modules with successive namespace blocks. Counting
all declarations under the first namespace would produce incorrect names.
"""
    spaces = re.findall(r'^namespace (\S+)', source, re.M)
    declarations = re.findall(r'^theorem (\S+)', source, re.M)
    if len(spaces) == 1:
        return [spaces[0] + '.' + name for name in declarations]
    blocks = re.findall(r'^namespace (\S+)\n(.*?)^end \1(?:\n|$)', source, re.M | re.S)
    if not spaces or len(blocks) != len(spaces):
        raise ValueError(f'Unrecognized namespace layout: {path}')
    result = []
    for space, body in blocks:
        if not space.startswith('TimeTraps.') or re.search(r'^namespace ', body, re.M):
            raise ValueError(f'Nested or nonproject namespace requires explicit support: {path}')
        result += [space + '.' + name for name in re.findall(r'^theorem (\S+)', body, re.M)]
    if len(result) != len(declarations):
        raise ValueError(f'Unassigned theorem: {path}')
    return result


def load_guard(project):
    spec = importlib.util.spec_from_file_location('release_proof_guard', project / 'scripts/lean_source_guard.py')
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    return guard


def source_check(bundle):
    manifest = json.loads((bundle / 'manifest.json').read_text())
    project = bundle / 'lean'
    certificate_path = bundle / manifest['source_certificate']
    if digest(certificate_path) != manifest['source_certificate_sha256']:
        raise ValueError('Terminal certificate hash mismatch')
    certificate = json.loads(certificate_path.read_text())
    pinned = {}
    for row in certificate['files'] + certificate['unchanged_baseline_research_files'] + certificate['logs_and_check_evidence']:
        if row['path'] in pinned and pinned[row['path']] != row['sha256']:
            raise ValueError('Conflicting certificate hashes')
        pinned[row['path']] = row['sha256']
    for row in manifest['files']:
        original = row.get('original_path')
        if original and original != 'audit/three-paper-closure-verification.json':
            if pinned.get(original) != row['sha256']:
                raise ValueError('Manifest is not bound to the terminal certificate: ' + original)
    for mk, ck in [('research_module_count','research_module_count'),
                   ('named_theorem_count','library_named_theorem_count'),
                   ('audited_declarations','audited_declarations'),
                   ('lean_version','lean_version'),('mathlib_revision','mathlib_revision'),
                   ('allowed_axioms','allowed_axioms')]:
        if manifest[mk] != certificate[ck]:
            raise ValueError('Manifest/certificate metadata mismatch: ' + mk)
    guard = load_guard(project)
    names = []
    located_names = []
    listed = {item['bundle_path']: item for item in manifest['files']}
    if len(listed) != len(manifest['files']):
        raise ValueError('Duplicate path in release manifest')
    for item in manifest['files']:
        path = bundle / item['bundle_path']
        if not path.is_file() or digest(path) != item['sha256']:
            raise ValueError(f'Missing or changed release file: {item["bundle_path"]}')
    modules = sorted(project.glob('TimeTraps/**/*.lean'))
    if len(modules) != manifest['research_module_count']:
        raise ValueError('Unexpected Lean module inventory')
    expected_modules = {p for p in pinned if p.startswith('TimeTraps/') and p.endswith('.lean')}
    if {p.relative_to(project).as_posix() for p in modules} != expected_modules:
        raise ValueError('Module paths differ from the terminal certificate')
    for path in modules + [project / 'TimeTraps.lean', project / 'Audit.lean',
                           project / 'lean-toolchain', project / 'lakefile.toml',
                           project / 'lake-manifest.json', project / 'scripts/lean_source_guard.py']:
        rel = path.relative_to(project).as_posix()
        entry = listed.get('lean/' + rel)
        if not entry or entry.get('original_path') != rel or digest(path) != pinned.get(rel):
            raise ValueError('Unbound or unlisted project file: ' + rel)
    for path in modules:
        source = path.read_text()
        if '\0' in source:
            raise ValueError(f'NUL byte: {path}')
        guard.assert_proof_source(source, path)
        current = theorem_names(guard.without_comments(source), path)
        names.extend(current)
        located_names.extend((name, path.relative_to(project).as_posix()) for name in current)
    guard.assert_proof_source((project / 'TimeTraps.lean').read_text(), 'TimeTraps.lean')
    if len(names) != len(set(names)) or len(names) != manifest['named_theorem_count']:
        raise ValueError('Duplicate or incorrect named theorem inventory')
    recorded = json.loads((bundle / 'theorem-index.json').read_text())
    if sorted(located_names) != sorted((row['name'], row['module']) for row in recorded):
        raise ValueError('Theorem index differs from source declarations')
    log = (bundle / manifest['archived_axiom_log']).read_text()
    audited = set(re.findall(r'AUDITED (\S+):', log))
    match = re.search(r'PASS: audited (\d+) TimeTraps declarations', log)
    if not match or int(match[1]) != manifest['audited_declarations']:
        raise ValueError('Archived transitive audit completion not found')
    if set(names) - audited:
        raise ValueError('A named theorem is absent from the archived audit')
    allowed = set(manifest['allowed_axioms'])
    vectors = re.findall(r'AUDITED [^:]+: \[([^]]*)\]', log)
    if len(vectors) != manifest['audited_declarations'] or len(audited) != manifest['audited_declarations']:
        raise ValueError('Archived audit declaration/vector count mismatch')
    for raw in vectors:
        if {a.strip() for a in raw.split(',') if a.strip()} - allowed:
            raise ValueError('Disallowed axiom in archived audit')
    return manifest, modules


def run_logged(command, project, logfile, environment):
    print('Running:', ' '.join(command), flush=True)
    with logfile.open('w') as output:
        result = subprocess.run(command, cwd=project, env=environment,
                                stdout=output, stderr=subprocess.STDOUT, check=False)
    if result.returncode:
        raise RuntimeError(f'Command failed ({result.returncode}); inspect {logfile}')
    text = logfile.read_text()
    if re.search(r'\bwarning:|\berror:|declaration uses .sorry.', text):
        raise RuntimeError(f'Warning or error in {logfile}')
    return {'command': command, 'exit_code': result.returncode,
            'log': str(logfile), 'log_sha256': digest(logfile)}


def lean_check(bundle, manifest, modules, memory):
    project = bundle / 'lean'
    if not shutil.which('lake'):
        raise RuntimeError('Install elan/Lean first, so lake is on PATH')
    # A clean-rebuild claim is made only when .lake was absent before this run.
    clean_start = not (project / '.lake').exists()
    out = bundle / 'reproduction' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    out.mkdir(parents=True, exist_ok=False)
    env = {**os.environ, 'LEAN_NUM_THREADS': '1'}
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=project,
                                      env=env, text=True).strip()
    if f'version {manifest["lean_version"]},' not in version:
        raise RuntimeError(f'Wrong project toolchain: {version}')
    records = []
    # lake lean is the pinned Lake file elaborator: it builds imports and
    # regenerates proper module import levels locally. No archived setup paths.
    for path in modules + [project / 'TimeTraps.lean', project / 'Audit.lean']:
        rel = path.relative_to(project).as_posix()
        command = ['lake', 'lean', rel, '--', '-j1', f'-M{memory}',
                   '-DwarningAsError=true', '-DautoImplicit=false']
        rec = run_logged(command, project, out / (rel.replace('/', '__') + '.log'), env)
        rec.update(file=rel, source_sha256=digest(path))
        records.append(rec)
    audit_text = (out / 'Audit.lean.log').read_text()
    audited = set(re.findall(r'AUDITED (\S+):', audit_text))
    names = json.loads((bundle / 'theorem-index.json').read_text())
    if {x['name'] for x in names} - audited:
        raise RuntimeError('Fresh Audit did not contain every named theorem')
    fresh_count = re.search(r'PASS: audited (\d+) TimeTraps declarations', audit_text)
    if not fresh_count:
        raise RuntimeError('Fresh transitive audit did not complete')
    if len(audited) != int(fresh_count[1]):
        raise RuntimeError('Fresh transitive audit count is inconsistent')
    mathlib = project / '.lake/packages/mathlib'
    revision = subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'], text=True).strip()
    dirty = subprocess.check_output(['git','-C',str(mathlib),'status','--porcelain'], text=True).strip()
    if revision != manifest['mathlib_revision'] or dirty:
        raise RuntimeError('Mathlib checkout is not the clean pinned revision')
    # Reject any source mutation during the reproduction run.
    source_check(bundle)
    report = {'completed_at_utc': datetime.now(timezone.utc).isoformat(),
              'record_kind': 'new portable exact-file reproduction',
              'clean_project_start': clean_start, 'lean_version_output': version,
              'all_sources_hash_unchanged': True, 'mathlib_revision': revision,
              'mathlib_checkout_clean': True, 'checks': records,
              'named_theorems_found_in_fresh_audit': len(names),
              'fresh_audited_declarations': int(fresh_count[1])}
    target = out / 'verification.json'
    target.write_text(json.dumps(report, indent=2) + '\n')
    print('Fresh Lean reproduction passed:', target)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    default = Path(__file__).resolve().parent.parent / 'source-bundle'
    if not default.is_dir():
        default = Path(__file__).resolve().parent.parent
    parser.add_argument('--bundle', type=Path, default=default)
    parser.add_argument('--lean', action='store_true', help='run all exact Lean files; substantial time/disk needed')
    parser.add_argument('--memory', type=int, default=4096, help='Lean per-process memory limit in MB')
    args = parser.parse_args()
    bundle = args.bundle.resolve()
    manifest, modules = source_check(bundle)
    print(f'Source/archived-evidence checks passed: {len(modules)} modules, '
          f'{manifest["named_theorem_count"]} named theorems. No new Lean build in this mode.')
    if args.lean:
        lean_check(bundle, manifest, modules, args.memory)


if __name__ == '__main__':
    main()
