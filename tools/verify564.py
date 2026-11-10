#!/usr/bin/env python3
"""Fresh 564-source reproduction; no project object reuse or certificate inference.
Requires Python >=3.11, pinned Lean/Lake, and cached locked dependencies.
The integrated declarations are compared globally by kernel name, with SHA256
fingerprints of the complete raw Expr UTF-8 strings (not pretty-printed types).
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
HELPERS = ['FullTreeAuditSupportFast', 'ExactKernelTypes']
APPS = ['SharpApplicationInstantiations', 'SharpApplicationFullyApplied', 'GeometricApplicationChecks']
PACKAGE_LIBS = {
    'mathlib': ['Mathlib'], 'plausible': ['Plausible'],
    'LeanSearchClient': ['LeanSearchClient'], 'importGraph': ['ImportGraph'],
    'proofwidgets': ['ProofWidgets'], 'aesop': ['Aesop'], 'Qq': ['Qq'],
    'batteries': ['Batteries'], 'Cli': ['Cli'],
}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def read(path):
    return json.loads(path.read_text())


def pinned_path(value):
    path = (ROOT / value).resolve()
    require(path.is_relative_to(ROOT), f'Path escapes repository: {value}')
    return path


def unique(rows, field, label):
    result = {}
    for row in rows:
        key = row[field]
        require(key not in result, f'Duplicate {label}: {key}')
        result[key] = row
    return result


def canonical(row):
    require(len(row['axioms']) == len(set(row['axioms'])), f'Duplicate axioms: {row["name"]}')
    return {key: (sorted(row[key]) if key == 'axioms' else row[key])
            for key in ['name', 'kind', 'universes', 'axioms', 'type_expr_sha256']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='New, nonexistent evidence directory')
    parser.add_argument('--check-sources-only', action='store_true')
    args = parser.parse_args()
    manifest_path = ROOT / 'lean/verification564/sources.json'
    manifest_hash = digest(manifest_path)
    manifest = read(manifest_path)
    mods = unique(manifest['modules'], 'module', 'module')
    require(manifest['module_count'] == len(mods) == 564, 'Expected 564 unique source modules')
    require(all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*', n) for n in mods), 'Invalid module name')
    required_tools = {'tools/verify564.py', *(f'tools/{n}.lean' for n in HELPERS + APPS)}
    require(required_tools <= set(manifest['tooling']), 'Missing pinned verifier/helper/application hashes')
    require({'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'} <= set(manifest['configuration']), 'Missing configuration hashes')
    expected_ref = manifest['expected_declarations']
    expected_path = pinned_path(expected_ref['path'])

    def inputs():
        require(digest(manifest_path) == manifest_hash, 'Source manifest changed during run')
        for row in mods.values():
            require(digest(pinned_path(row['path'])) == row['sha256'], f'Source changed: {row["path"]}')
        for name, sha in manifest['configuration'].items():
            require(digest(pinned_path('lean/' + name)) == sha, f'Configuration changed: {name}')
        for name, sha in manifest['tooling'].items():
            require(digest(pinned_path(name)) == sha, f'Tooling changed: {name}')
        require(digest(expected_path) == expected_ref['sha256'], 'Expected declarations hash mismatch')

    inputs()
    config = tomllib.loads((ROOT / 'lean/lakefile.toml').read_text())
    roots = [n for lib in config['lean_lib'] for n in lib['roots']]
    require(len(roots) == len(set(roots)) == 564 and set(roots) == set(mods), 'Lake roots do not match source manifest')
    expected_doc = read(expected_path)
    expected = unique(expected_doc['records'], 'name', 'expected kernel name')
    require(expected_doc['schema_version'] == 1 and expected_doc['module_count'] == 564 and
            expected_doc['declaration_count'] == len(expected) == 7979, 'Invalid pinned declaration inventory')
    expected = {name: canonical(row) for name, row in expected.items()}
    require(all(re.fullmatch(r'[0-9a-f]{64}', r['type_expr_sha256']) for r in expected.values()), 'Invalid raw Expr SHA256')
    require(all(r['kind'] != 'axiom' and set(r['axioms']) <= ALLOWED for r in expected.values()), 'Unexpected pinned axiom')
    if args.check_sources_only:
        print('PASS: 564 source hashes, configuration, helpers and pinned 7979-declaration manifest. No Lean build or audit performed.')
        return
    require(args.output is not None, 'Supply --output pointing to a new directory')
    out = args.output.resolve()
    out.mkdir(exist_ok=False, parents=True)
    for name in ['objects', 'helpers', 'audits', 'exact_types', 'logs']:
        (out / name).mkdir()
    lean = os.environ.get('LEAN_BIN') or shutil.which('lean')
    require(lean is not None, 'Set LEAN_BIN or put Lean on PATH')
    version = subprocess.check_output([lean, '--version'], text=True)
    require(re.search(r'\bversion 4\.35\.0(?:\s|,|$)', version), f'Unexpected Lean version: {version}')
    packages = Path(os.environ.get('MATHLIB_PACKAGES', ROOT / 'lean/.lake/packages')).resolve()
    pins = read(ROOT / 'lean/lake-manifest.json')['packages']
    require(set(unique(pins, 'name', 'locked package')) == set(PACKAGE_LIBS), 'Unexpected locked package set')

    def check_pins():
        for row in pins:
            require(row['type'] == 'git', f'Non-git package: {row["name"]}')
            directory = packages / row['name']
            rev = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
            require(rev == row['rev'], f'Package revision mismatch: {row["name"]}')
            dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True)
            require(not dirty.strip(), f'Tracked package modifications: {row["name"]}')
    check_pins()
    # Cache setup and explicit locked Cli build are prerequisites, not actions
    # performed by this verifier. Require every locked library directory.
    package_paths = [packages / row['name'] / '.lake/build/lib/lean' for row in pins]
    for lib in package_paths:
        require(lib.is_dir(), f'Missing package library: {lib}; run pinned cache setup and explicit Cli build as documented')
        for name in [*mods, *HELPERS]:
            require(not (lib / (name.replace('.', '/') + '.olean')).exists(), f'Shadow project/helper object: {name} in {lib}')
    # Fingerprint all externally loaded library artifacts before and after audit.
    def dependency_snapshot():
        return {str(p.relative_to(packages)): digest(p)
                for lib in package_paths for p in sorted(lib.rglob('*')) if p.is_file()}
    before = dependency_snapshot()
    (out / 'dependency_hashes.json').write_text(json.dumps(before, indent=2) + '\n')
    objects = out / 'objects'
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [objects, out / 'helpers', *sorted(package_paths)]))
    (out / 'LEAN_PATH').write_text(env['LEAN_PATH'] + '\n')

    def run(argv, cwd, log):
        with log.open('w') as f:
            subprocess.run([lean, *argv], cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, check=True)

    order, records, pending = [], {}, set(mods)
    while pending:
        ready = sorted(n for n in pending if not (set(mods[n]['imports']) & pending))
        require(ready, 'Cyclic source imports')
        for name in ready:
            source = pinned_path(mods[name]['path'])
            obj = objects / (name.replace('.', '/') + '.olean')
            obj.parent.mkdir(parents=True, exist_ok=True)
            log = out / 'logs' / (name + '.compile.log')
            run(['--deps', str(source)], ROOT / 'lean', out / 'logs' / (name + '.deps.log'))
            run(['-o', str(obj), str(source)], ROOT / 'lean', log)
            records[name] = {'source_sha256': digest(source), 'object_sha256': digest(obj), 'compile_log_sha256': digest(log)}
            print('Compiled', name, flush=True)
        order.extend(ready)
        pending.difference_update(ready)
    for helper in HELPERS:
        source = ROOT / 'tools' / (helper + '.lean')
        run(['-o', str(out / 'helpers' / (helper + '.olean')), str(source)], source.parent, out / 'logs' / (helper + '.log'))
    driver = out / 'Audit.lean'
    targets = ', '.join(order)
    driver.write_text('\n'.join([
        *('import ' + n for n in [*HELPERS, *order]),
        'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
        *('set_option pp.' + n + ' true' for n in ['fullNames', 'universes', 'explicit', 'deepTerms']),
        'set_option pp.notation false', 'set_option pp.maxSteps 1000000',
        '#verify_full_tree_inventory [' + targets + '] to ' + json.dumps(str(out / 'inventory.json')),
        *('#fast_full_tree_audit ' + n + ' to ' + json.dumps(str(out / 'audits' / (n + '.json'))) for n in order),
        '#exact_kernel_types [' + targets + '] to ' + json.dumps(str(out / 'exact_types')),
    ]) + '\n')
    run([str(driver)], out, out / 'logs/audit.log')
    inventory = read(out / 'inventory.json')
    require(inventory['all_match'] and inventory['module_count'] == 564, 'Kernel inventory failed')
    by_module = unique(inventory['modules'], 'module', 'inventory module')
    require(set(by_module) == set(mods), 'Inventory module set mismatch')
    actual = {}
    content = (out / 'logs/audit.log').read_text()
    for name in order:
        audit = read(out / 'audits' / (name + '.json'))
        rows = unique(audit['records'], 'name', 'audited kernel name')
        names = set(rows)
        inv_names = by_module[name]['kernel_names']
        require(audit['module'] == name and audit['environment_constant_count'] == len(rows), f'Audit count mismatch: {name}')
        require(by_module[name]['matches_full_kernel_scan'] and len(inv_names) == len(set(inv_names)) == len(rows) and set(inv_names) == names, f'Kernel names mismatch: {name}')
        raw_doc = read(out / 'exact_types' / (name + '.json'))
        raw = unique(raw_doc['records'], 'name', 'raw kernel name')
        require(raw_doc['module'] == name and raw_doc['count'] == len(rows) and set(raw) == names, f'Raw type inventory mismatch: {name}')
        for kernel_name, row in rows.items():
            require(kernel_name not in actual, f'Globally duplicate kernel name: {kernel_name}')
            require(row['module'] == name and row['builtin_check_and_print_axioms_invoked'] is True, f'Missing builtin check: {kernel_name}')
            require(row['kind'] != 'axiom' and set(row['axioms']) <= ALLOWED, f'Unexpected axiom: {kernel_name}')
            require(row['universes'] == raw[kernel_name]['universes'], f'Raw/audit universe mismatch: {kernel_name}')
            for marker in ['BEGIN', 'END']:
                require(content.count(f'FULL_TREE_PAIR_{marker} {kernel_name}\n') == 1, f'Builtin marker mismatch: {kernel_name}')
            actual[kernel_name] = canonical({**row, 'type_expr_sha256': hashlib.sha256(raw[kernel_name]['type_expr_repr'].encode('utf-8')).hexdigest()})
        records[name].update(audit_sha256=digest(out / 'audits' / (name + '.json')), raw_types_sha256=digest(out / 'exact_types' / (name + '.json')))
    require(set(actual) == set(expected), 'Global declaration-name inventory differs from pinned integration')
    mismatches = [n for n in expected if actual[n] != expected[n]]
    require(not mismatches, f'Pinned raw type/universe/kind/axiom mismatch: {mismatches[:20]}')
    require(len(actual) == 7979 and 'EXACT_KERNEL_TYPES_DONE 564 7979' in content, 'Final declaration count mismatch')
    for app in APPS:
        run([str(ROOT / 'tools' / (app + '.lean'))], ROOT / 'tools', out / 'logs' / (app + '.log'))
    require('GEOMETRIC_APPLICATION_CHECKS_PASSED' in (out / 'logs/GeometricApplicationChecks.log').read_text(), 'Missing geometric check marker')
    inputs()
    check_pins()
    require(before == dependency_snapshot(), 'Dependency library artifacts changed during project verification')
    result = {'passed': True, 'scope': 'Fresh compilation of all 564 sources and complete kernel audit in this separate portable run',
              'modules': 564, 'declarations': 7979, 'reused_project_objects': 0,
              'allowed_axioms': sorted(ALLOWED), 'global_exact_manifest_match': True,
              'source_manifest_sha256': manifest_hash, 'expected_declarations_sha256': expected_ref['sha256'],
              'application_checks': APPS, 'records': records}
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: 564 freshly compiled modules; 7979 declarations match pinned kernel contents')


if __name__ == '__main__':
    main()
