"""Compile the delivered dependency graph and record actual proof-checking evidence.

Each module is compiled by Lean directly, with output redirected to a log file
(no OS pipes: the workspace sandbox denies pipe creation).
"""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import sys

from leanlib import LEAN, ROOT, check_environment, lean_env

MODULES = [
    'Abel', 'Constant', 'TournamentSequence', 'Application', 'Descent',
    'Radial', 'Normalization', 'Evaluation', 'StandardAlgebraicity', 'Main',
    'WeightedAbel', 'Corollaries', 'QuadraticAbel', 'Remainder',
    'QRegular', 'MatrixPowerSeries', 'QRegularApplications', 'PathCountGrowth',
    'RationalRadial', 'RationalLinearDescent', 'RationalSeriesLimit', 'QRegularRationalLimit',
    'OrderedCancellation', 'ColorEnergy', 'ColorTransport', 'EndpointCheck',
]


def dependency_order(modules):
    pending = list(modules)
    for name in pending:
        if not (ROOT / (name + '.lean')).is_file():
            raise FileNotFoundError('Missing delivered module: ' + name)
    remaining, ordered = set(pending), []
    while remaining:
        ready = sorted(name for name in remaining if not (
            set(re.findall(r'^import\s+(\w+)\s*$',
                           (ROOT / (name + '.lean')).read_text(encoding='utf-8'), re.M))
            & remaining))
        if not ready:
            raise RuntimeError('Cyclic local imports')
        ordered.extend(ready)
        remaining.difference_update(ready)
    return ordered


def compile_module(name, logdir):
    log = logdir / (name + '.log')
    with open(log, 'w', encoding='utf-8') as handle:
        proc = subprocess.run([str(LEAN), '-o', name + '.olean', name + '.lean'],
                              cwd=ROOT, env=lean_env(),
                              stdout=handle, stderr=subprocess.STDOUT)
    output = log.read_text(encoding='utf-8')
    return proc.returncode, output


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    check_environment()
    ordered = dependency_order(MODULES)
    logdir = ROOT / 'verification'
    logdir.mkdir(exist_ok=True)
    records = []
    for name in ordered:
        code, output = compile_module(name, logdir)
        passed = code == 0 and 'sorryAx' not in output and 'error' not in output.lower()
        records.append({
            'module': name,
            'exit_code': code,
            'passed': passed,
            'source_sha256': hashlib.sha256((ROOT / (name + '.lean')).read_bytes()).hexdigest(),
            'axiom_reports': re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^\]]*\]", output, re.S),
        })
        print(f'{name}: {"PASS" if passed else "FAIL"}', flush=True)
        if not passed:
            print(output, flush=True)
            break
    result = {
        'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'lean_version': (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip(),
        'mathlib_commit': '56a005855ea17e0b0958f73ec801ae140b0a1679',
        'modules_built': [r['module'] for r in records],
        'all_delivered_modules_checked': len(records) == len(ordered) and all(r['passed'] for r in records),
        'records': records,
        'scope': ('The main application keeps the graph-theoretic asymptotic and the finite '
                  'Lindemann-Weierstrass input as explicit hypotheses. Passing does not prove '
                  'those two external theorems. OrderedCancellation verifies the abstract filtered '
                  'ring and finite-packet recursion only; it does not formalize tournament '
                  'kernel costs, permanent recovery, or Condition R. ColorEnergy verifies finite '
                  'prefix-energy algebra only. ColorTransport proves actual word reachability '
                  'and an area lower bound, not optimal area attainment or graph-edit bounds.'),
    }
    (logdir / 'result.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n',
                                       encoding='utf-8')
    print('ALL MODULES PASSED' if result['all_delivered_modules_checked'] else 'VERIFICATION INCOMPLETE')
    return 0 if result['all_delivered_modules_checked'] else 1


if __name__ == '__main__':
    sys.exit(main())
