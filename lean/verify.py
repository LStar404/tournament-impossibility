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
    'OrderedCancellation', 'ColorEnergy', 'ColorTransport', 'DiamondGap', 'ColorTransportExact', 'ColorGraphRepair', 'ColorCutNormalization', 'ColorTargetModels', 'TournamentColorEnumeration', 'DiamondFreeRepresentation', 'FiniteGraphEditTransport', 'ZeroDiamondRepair', 'VectorWeakMajorization', 'MajorizationCone', 'SelectedWeight', 'BalancedSignCounts', 'SelectedSignPairs', 'SelectedRowOptimization', 'TournamentEnvelope', 'TournamentSwitching', 'TopAbsoluteSelection', 'SelectedTournamentMajorization', 'VectorMajorizationEndpoint', 'IteratedVectorMajorization', 'TournamentPowerComparison', 'ReferenceSquare', 'TransitiveOrbit', 'KMatrixIdentification', 'ZigzagReference', 'SignedConjugacy', 'ReferenceDiagonal', 'SignedReferenceConjugacy', 'BasisReference', 'ReferenceMomentComparison', 'ReferenceMomentEndpoint', 'SignedVectorOrbit', 'SignedCycleOnes', 'ZigzagOnes', 'ReferenceOnesOrbit', 'TournamentEnergySeries', 'TournamentEnergyConvergence', 'TournamentEnergyRowDomain', 'OnesEnergyEndpoint', 'TournamentGramGeometric', 'ResolventSeriesIdentity', 'TournamentSourceResolvent', 'SourceResolventEndpoint', 'OrdinalSixthPolynomial', 'OrdinalSixthPolynomialEndpoint', 'TwoBlockEnergy', 'RectangularFrobenius', 'TwoBlockCubeGeneric', 'TwoBlockSixthMoment', 'OrdinalMomentRecurrence', 'OrdinalBlockMatrix', 'OrdinalSixthMatrixBridge', 'OrdinalSixthMatrixEndpoint', 'TournamentHamiltonian.Packing', 'TournamentHamiltonian.Definitions', 'TournamentHamiltonian.PositiveDeterminant', 'TournamentHamiltonian.Hadamard', 'TournamentHamiltonian.Orientation', 'TournamentHamiltonian.PathConvolution', 'TournamentHamiltonian.PathConvolutionCoefficients', 'TournamentHamiltonian.PathConvolutionGenerating', 'ActualPathConvolution', 'TransitiveFirstEnergy', 'TournamentSourceEnergy', 'SmallBlockSixthEstimate', 'OrdinalTournamentDeficit', 'OrdinalTransitiveReference', 'OrdinalGlobalSixthDeficit', 'GlobalSixthDeficitEndpoint', 'TournamentHamiltonian.TransitiveDeterminant', 'DiamondFreeDeterminant', 'PermanentDiagonalExpansion', 'DiamondFreePathAverage', 'DiamondTriangleIncidence', 'TriangleCountBridge', 'StrongTournamentTriangles', 'OrdinalTriangleAdditivity', 'DiamondLinkAverage', 'PivotCycleLink', 'PivotSmallDiamond', 'IntegerCycleSumBridge', 'PivotMomentInvariant', 'TournamentComponents', 'TournamentComponentBlocks', 'SmallDiamondPivotReduction', 'SmallDiamondComponentReduction', 'SmallDiamondGraphEndpoint', 'TournamentOrdinalReconstruction', 'ActualSmallDiamondSixth', 'DiamondFreeKernelDeterminant', 'DiamondFreeKernelLimit', 'DiamondFreeKernelUniform', 'DiamondFreeComplexResolvent', 'ComplexBinomialRate', 'ComplexOperatorResolventBound', 'EndpointCheck',
]


def dependency_order(modules):
    pending = list(modules)
    for name in pending:
        if not (ROOT / (name.replace('.', '/') + '.lean')).is_file():
            raise FileNotFoundError('Missing delivered module: ' + name)
    remaining, ordered = set(pending), []
    while remaining:
        ready = sorted(name for name in remaining if not (
            set(re.findall(r'^import\s+([\w.]+)\s*$',
                           (ROOT / (name.replace('.', '/') + '.lean')).read_text(encoding='utf-8'), re.M))
            & remaining))
        if not ready:
            raise RuntimeError('Cyclic local imports')
        ordered.extend(ready)
        remaining.difference_update(ready)
    return ordered


def compile_module(name, logdir):
    log = logdir / (name + '.log')
    with open(log, 'w', encoding='utf-8') as handle:
        proc = subprocess.run([str(LEAN), '-o', name.replace('.', '/') + '.olean', name.replace('.', '/') + '.lean'],
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
    # Optional continuation after interruption. Reuse only successful records
    # whose exact source hash and retained log still match the evidence.
    reusable = {}
    reused_modules = []
    previous_checked_at = None
    old_path = logdir / 'result.json'
    if '--resume' in sys.argv and old_path.exists():
        old = json.loads(old_path.read_text(encoding='utf-8'))
        previous_checked_at = old.get('checked_at_utc')
        if old.get('lean_version') == (ROOT / 'lean-toolchain').read_text().strip() and old.get('mathlib_commit') == '56a005855ea17e0b0958f73ec801ae140b0a1679':
            reusable = {r['module']: r for r in old.get('records', []) if r.get('passed') and r.get('exit_code') == 0}
    reuse_prefix = True
    for name in ordered:
        previous = reusable.get(name)
        source_hash = hashlib.sha256((ROOT / (name.replace('.', '/') + '.lean')).read_bytes()).hexdigest()
        retained_log = logdir / (name + '.log')
        if reuse_prefix and previous and previous.get('source_sha256') == source_hash and retained_log.is_file() and 'sorryAx' not in retained_log.read_text(encoding='utf-8'):
            records.append(previous)
            reused_modules.append(name)
            print(f'{name}: PASS (retained exact-source check)', flush=True)
            continue
        # A changed prerequisite invalidates every later cached result.
        reuse_prefix = False
        code, output = compile_module(name, logdir)
        # Lean's exit status identifies diagnostics; theorem names can contain 'error'.
        passed = code == 0 and 'sorryAx' not in output
        records.append({
            'module': name,
            'exit_code': code,
            'passed': passed,
            'source_sha256': hashlib.sha256((ROOT / (name.replace('.', '/') + '.lean')).read_bytes()).hexdigest(),
            'axiom_reports': re.findall(r"'[^'\n]+' depends on axioms:\s*\[[^\]]*\]", output, re.S),
        })
        print(f'{name}: {"PASS" if passed else "FAIL"}', flush=True)
        if not passed:
            print(output, flush=True)
            break
    result = {
        'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'retained_exact_source_checks': reused_modules,
        'retained_checks_from_utc': previous_checked_at if reused_modules else None,
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
                  'and an area lower bound. ColorTransportExact proves attained minimum distance '
                  'and color-word energy repair paths. ColorGraphRepair supplies matrix energy '
                  'and actual finite differing-edge bounds for normalized color-word tournaments, '
                  'extended by ColorCutNormalization to arbitrary color words. ColorTargetModels '
                  'supplies independent carousel/doubling isomorphisms. DiamondFreeRepresentation '
                  'constructs a color-word representation from the actual zero diamond count; '
                  'ZeroDiamondRepair exports original-tournament finite differing-edge bounds '
                  'to independent carousel/doubling targets for D=0. Positive-diamond '
                  'repair and Condition R remain outside this result. '
                  'DiamondGap proves only finite tournament diamond coverage and D=0 or n<=4D; '
                  'this does not imply Condition R. VectorWeakMajorization verifies finite Abel, '
                  'square-sum comparison and a signed matrix bound. The cone/sign/selection modules '
                  'prove K cone/prefix preservation and the combinatorial envelope<=P_k, '
                  'and SelectedTournamentMajorization completes actual finite tournament vector '
                  'weak majorization, independently checked from raw matrix entries. '
                  'ReferenceMomentComparison supplies the concrete K-square conjugacy and all '
                  'nonnegative-integer-power Frobenius comparisons. Negative/fractional powers, '
                  'small-defect sixth-order identities and Condition R are not proved. ReferenceOnesOrbit '
                  'identifies the actual all-ones orbit; TournamentEnergyRowDomain proves source-energy '
                  'series convergence and comparison for q>=0 with q*(n-1)^2<1, including q=1/n^2 '
                  'for n>0 without a Summable premise. TournamentSourceResolvent proves the actual source resolvent identity, both inverse identities, and comparison on that same real nonnegative row domain. No enlarged complex domain or full R is asserted. OrdinalSixthPolynomial proves only explicit polynomial subtraction and conditional scalar transfer, with the actual ordinal-matrix sixth-moment identification now supplied by OrdinalSixthMatrixBridge for arbitrary finite skew block families. TournamentSourceEnergy identifies directed cycle counts/3 with the source deficit, and OrdinalGlobalSixthDeficit proves the actual global-transitive-reference sixth deficit formula. The small-block bound retains explicit size and D-versus-triangle assumptions; DiamondTriangleIncidence proves D<=(n-3)t for actual unordered counts, and SmallDiamondComponentReduction proves actual source-switched SCC size bounds for positive small D. TournamentOrdinalReconstruction proves actual ordered SCC matrix reconstruction. ActualSmallDiamondSixth proves the actual sixth-deficit lower bound 6*n^2*D for n>=4, D>0, 24*D<=n^2 with no decomposition/count/moment assumptions. Full analytic R remains outside scope. ActualPathConvolution proves exact S1 even-subset convolution for this repository hamiltonianPathCount, with no convolution assumption; DiamondFreePathAverage proves the exact normalized two-permanent average for the original hamiltonianPathCount under the actual zero diamond count, without principal-minor or convolution assumptions; no asymptotic recovery or R is implied. DiamondFreeKernelDeterminant proves the full finite determinant polynomial for actual zero-diamond tournaments over every characteristic-zero field; no complex-domain convergence or analytic R follows from that finite module alone. DiamondFreeKernelLimit proves moving-parameter cosh/cos determinant limits and eventual true inverses; DiamondFreeKernelUniform upgrades to qualitative compact-uniform convergence and scalar reciprocal convergence off cosine zeros. DiamondFreeComplexResolvent proves exact quadratic-kernel factorization and eventual two-sided matrix inverses off limiting cosine zeros. No rate, inverse operator norm, source-quadratic-form estimate, derivative limit, or analytic R is asserted by those qualitative modules. ComplexBinomialRate separately proves the actual zero-diamond imaginary determinant error <=2*exp(R)*R^2/n when n>0, R/n<=1/2 and R^2/n<=1. ComplexOperatorResolventBound proves true Hilbert operator Neumann inverse and source bounds under an explicit operator-norm smallness hypothesis; the graph-to-operator bound is not supplied.'),
    }
    (logdir / 'result.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n',
                                       encoding='utf-8')
    print('ALL MODULES PASSED' if result['all_delivered_modules_checked'] else 'VERIFICATION INCOMPLETE')
    return 0 if result['all_delivered_modules_checked'] else 1


if __name__ == '__main__':
    sys.exit(main())
