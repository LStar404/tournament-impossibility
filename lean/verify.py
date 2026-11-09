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
    'OrderedCancellation', 'ColorEnergy', 'ColorTransport', 'DiamondGap', 'ColorTransportExact', 'ColorGraphRepair', 'ColorCutNormalization', 'ColorTargetModels', 'TournamentColorEnumeration', 'DiamondFreeRepresentation', 'FiniteGraphEditTransport', 'ZeroDiamondRepair', 'VectorWeakMajorization', 'MajorizationCone', 'SelectedWeight', 'BalancedSignCounts', 'SelectedSignPairs', 'SelectedRowOptimization', 'TournamentEnvelope', 'TournamentSwitching', 'TopAbsoluteSelection', 'SelectedTournamentMajorization', 'VectorMajorizationEndpoint', 'IteratedVectorMajorization', 'TournamentPowerComparison', 'ReferenceSquare', 'TransitiveOrbit', 'KMatrixIdentification', 'ZigzagReference', 'SignedConjugacy', 'ReferenceDiagonal', 'SignedReferenceConjugacy', 'BasisReference', 'ReferenceMomentComparison', 'ReferenceMomentEndpoint', 'SignedVectorOrbit', 'SignedCycleOnes', 'ZigzagOnes', 'ReferenceOnesOrbit', 'TournamentEnergySeries', 'TournamentEnergyConvergence', 'TournamentEnergyRowDomain', 'OnesEnergyEndpoint', 'TournamentGramGeometric', 'ResolventSeriesIdentity', 'TournamentSourceResolvent', 'SourceResolventEndpoint', 'OrdinalSixthPolynomial', 'OrdinalSixthPolynomialEndpoint', 'TwoBlockEnergy', 'RectangularFrobenius', 'TwoBlockCubeGeneric', 'TwoBlockSixthMoment', 'OrdinalMomentRecurrence', 'OrdinalBlockMatrix', 'OrdinalSixthMatrixBridge', 'OrdinalSixthMatrixEndpoint', 'TournamentHamiltonian.Packing', 'TournamentHamiltonian.Definitions', 'TournamentHamiltonian.PositiveDeterminant', 'TournamentHamiltonian.Hadamard', 'TournamentHamiltonian.Orientation', 'TournamentHamiltonian.PathConvolution', 'TournamentHamiltonian.PathConvolutionCoefficients', 'TournamentHamiltonian.PathConvolutionGenerating', 'ActualPathConvolution', 'TransitiveFirstEnergy', 'TournamentSourceEnergy', 'SmallBlockSixthEstimate', 'OrdinalTournamentDeficit', 'OrdinalTransitiveReference', 'OrdinalGlobalSixthDeficit', 'GlobalSixthDeficitEndpoint', 'TournamentHamiltonian.TransitiveDeterminant', 'DiamondFreeDeterminant', 'PermanentDiagonalExpansion', 'DiamondFreePathAverage', 'DiamondTriangleIncidence', 'TriangleCountBridge', 'StrongTournamentTriangles', 'OrdinalTriangleAdditivity', 'DiamondLinkAverage', 'PivotCycleLink', 'PivotSmallDiamond', 'IntegerCycleSumBridge', 'PivotMomentInvariant', 'TournamentComponents', 'TournamentComponentBlocks', 'SmallDiamondPivotReduction', 'SmallDiamondComponentReduction', 'SmallDiamondGraphEndpoint', 'TournamentOrdinalReconstruction', 'ActualSmallDiamondSixth', 'DiamondFreeKernelDeterminant', 'DiamondFreeKernelLimit', 'DiamondFreeKernelUniform', 'DiamondFreeComplexResolvent', 'ComplexBinomialRate', 'ComplexOperatorResolventBound', 'TransitiveKernelInverse', 'MatrixEuclideanEntryBound', 'TransitiveKernelInverseBounds', 'DiamondFreeKernelInverseTransfer', 'DiamondFreeKernelOperatorBound', 'ComplexKernelDiskLower', 'DiamondFreeDiskResolvent', 'ActualComplexScoreSource', 'GaussianParameterBranch', 'GaussianSourceExponent', 'ComplexResolventAnalytic', 'ComplexCauchyErrorTransfer', 'GaussianScalarFactor', 'ActualGaussianSourceExponent', 'GaussianDeterminantBranch', 'GaussianSourceProduct', 'GaussianSourceAnalytic', 'GaussianSourceDerivative', 'ComplexSkewSourceIdentity', 'BlockGaussianDeterminant', 'BlockGaussianSourceElimination', 'RawBlockSourceIdentity', 'RawGaussianSourceScalar', 'ActualBlockGaussianSource', 'BipartitePairingPermanent', 'WickPairingZero', 'WickBipartiteEquiv', 'WickPairingPermanent', 'RectangularPairing', 'FinitePairingTransport', 'FinitePairingPermanent', 'SubsetPairingPermanent', 'SubsetPairingScaling', 'FrozenPartialPairingPolynomial', 'ShiftedProductSubsetExpansion', 'SquarefreePairingContraction', 'FrozenPairingEndpoints', 'RepeatedLabelPairing', 'FullFourthMoment', 'SymmetricPairingTransport', 'PairingRepresentativeBridge', 'OccurrenceWickPolynomial', 'OccurrenceSquarefreeEquiv', 'OrderedUnorderedSubsetPairing', 'FullWickSquarefreeCompatibility', 'PairingDeletion', 'PairingMomentRecurrence', 'PairingMomentParity', 'ConstantPairingMoments', 'ConstantPairingCount', 'ConstantPairingFormalExponential', 'ScalarWickFormalExponential', 'LinearSourceOccurrences', 'LinearSourceExpansion', 'PairingEndpointEquiv', 'LinearSourcePairingFactor', 'MultivariateLinearFormalExponential', 'RankOneQuadraticCoefficients', 'RankOneQuadraticODE', 'RankOneQuadraticUnitBranch', 'RankOneQuadraticDeterminant', 'AssignmentDeletionExponent', 'OptionPairingDeletion', 'FullWickMonomialRecurrence', 'FullWickPolynomialIBP', 'FormalLinearLift', 'FormalDividedPowers', 'FormalMixedExponential', 'MixedSourcePolynomials', 'FormalWickInsertion', 'ActualMixedSourceWard', 'ActualMixedWardMatrix', 'MixedWardUnit', 'MixedFormalTimeDerivative', 'MixedWardSolution', 'ActualMixedSourceTimeODE', 'DerivationFiniteProduct', 'DerivationDeterminantColumns', 'FullJacobiDerivation', 'FormalFirstOrderUniqueness', 'NormalizedDeterminantBranch', 'ActualMixedDeterminantJacobi', 'ActualDeterminantBranchDerivative', 'MatrixDerivationInverse', 'MixedCovarianceSymmetry', 'MixedCovarianceDerivative', 'MixedSourceQuadraticDerivative', 'MixedDeterminantCandidateODE', 'ActualMixedDeterminantFormula', 'MixedEvenMatrix', 'MixedEvenCandidate', 'ActualMixedEvenDescent', 'RawFormalMixedSpecialization', 'TournamentRawFormalWick', 'AnalyticNormalizedBranch', 'AnalyticTaylorArithmetic', 'AnalyticTaylorFinite', 'AnalyticTaylorInverse', 'AffineMatrixTaylorBridge', 'AnalyticTaylorBranch', 'ActualGaussianTaylorBranch', 'TaylorDerivativeExponential', 'RawSourceTaylorBridge', 'TournamentRawWickAnalytic', 'ActualProductWickGerm', 'WickAnalyticDiskTransfer', 'ActualWickUniformDisk', 'WickCoefficientCauchy', 'ActualWickCoefficientBounds', 'WickGeometricTruncation', 'ActualWickTruncation', 'PolynomialInsertionWard', 'PolynomialTiltedRecurrence', 'PhysicalTiltedCovariance', 'OccurrenceWordDerivative', 'PhysicalWordRecurrence', 'PhysicalWordEvenDescent', 'PhysicalWordCoefficientOrder', 'AlgebraFormalExponential', 'FactorizedResidualIdentity', 'ResidualLowCoefficients', 'ResidualInsertionConvolution', 'EndpointCheck',
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
                  'for n>0 without a Summable premise. TournamentSourceResolvent proves the actual source resolvent identity, both inverse identities, and comparison on that same real nonnegative row domain. No enlarged complex domain or full R is asserted. OrdinalSixthPolynomial proves only explicit polynomial subtraction and conditional scalar transfer, with the actual ordinal-matrix sixth-moment identification now supplied by OrdinalSixthMatrixBridge for arbitrary finite skew block families. TournamentSourceEnergy identifies directed cycle counts/3 with the source deficit, and OrdinalGlobalSixthDeficit proves the actual global-transitive-reference sixth deficit formula. The small-block bound retains explicit size and D-versus-triangle assumptions; DiamondTriangleIncidence proves D<=(n-3)t for actual unordered counts, and SmallDiamondComponentReduction proves actual source-switched SCC size bounds for positive small D. TournamentOrdinalReconstruction proves actual ordered SCC matrix reconstruction. ActualSmallDiamondSixth proves the actual sixth-deficit lower bound 6*n^2*D for n>=4, D>0, 24*D<=n^2 with no decomposition/count/moment assumptions. Full analytic R remains outside scope. ActualPathConvolution proves exact S1 even-subset convolution for this repository hamiltonianPathCount, with no convolution assumption; DiamondFreePathAverage proves the exact normalized two-permanent average for the original hamiltonianPathCount under the actual zero diamond count, without principal-minor or convolution assumptions; no asymptotic recovery or R is implied. DiamondFreeKernelDeterminant proves the full finite determinant polynomial for actual zero-diamond tournaments over every characteristic-zero field; no complex-domain convergence or analytic R follows from that finite module alone. DiamondFreeKernelLimit proves moving-parameter cosh/cos determinant limits and eventual true inverses; DiamondFreeKernelUniform upgrades to qualitative compact-uniform convergence and scalar reciprocal convergence off cosine zeros. DiamondFreeComplexResolvent proves exact quadratic-kernel factorization and eventual two-sided matrix inverses off limiting cosine zeros. No rate, inverse operator norm, source-quadratic-form estimate, derivative limit, or analytic R is asserted by those qualitative modules. ComplexBinomialRate separately proves the actual zero-diamond imaginary determinant error <=2*exp(R)*R^2/n when n>0, R/n<=1/2 and R^2/n<=1. ComplexOperatorResolventBound proves true Hilbert operator Neumann inverse and source bounds under an explicit operator-norm smallness hypothesis; that generic module alone does not supply the graph-to-operator bound. The TransitiveKernelInverse and bounds modules now derive exact inverse entries, and MatrixEuclideanEntryBound plus actual sign-switch/relabel transfer prove a genuine graph inverse norm bound. ComplexKernelDiskLower proves explicit and eventual graph-independent disk thresholds. DiamondFreeDiskResolvent proves true two-sided quadratic inverses and uniform Euclidean inverse/source bounds on each fixed disk R<pi/2, conditional only on zero diamonds and stated linear source energy. ActualComplexScoreSource identifies real score energy and the ordinary transpose source expression. The Gaussian modules additionally prove parameter substitution with the principal logarithm of beta, the origin-normalized determinant branch identity, and uniform O(1/n) errors for the explicit Gaussian/source proxy and each fixed derivative on nested disks, uniformly in actual zero-diamond graphs and |v|<=1 under stated linear score energy. Actual analyticity and source estimates are proved internally. ActualBlockGaussianSource now proves the true doubled-block bilinear source elimination and determinant-branch bridge for v^2=1, n>0, beta nonzero and a true quadratic resolvent unit, exactly identifying the algebraic factor with the analytic proxy. This is finite algebra, not formal Gaussian pairing resummation or a probability integral with indefinite covariance. WickPairingPermanent additionally proves the finite sum over all fixed-point-free involutive pairings for a bipartite covariance equals the matrix permanent, with monochromatic weights eliminated, a proved pairing-permutation equivalence, unique edge representatives and the empty case. This is not a probability expectation or partial-pairing/exponential resummation theorem. The finite pairing modules further prove actual transport over arbitrary finite left/right types, vanishing for unequal cardinalities, and equal-cardinality subset pairing sums as enumerated submatrix permanents. The next finite modules prove actual subset-weight scaling, frozen coefficient grouping, the shifted-product subset expansion, and an explicit linear squarefree coefficient contraction connecting that product to the frozen polynomial, including F0=1 and degree at most n. The occurrence-pairing modules additionally retain repeated labels, prove the full fourth pairing formula, arbitrary position transport for symmetric covariance, compatibility with unique edge representatives, and the full polynomial linear Wick definition via occurrence types with monomial and enumeration theorems. FullWickSquarefreeCompatibility now identifies full Wick on the actual shifted product with the squarefree contraction and frozen polynomial. PairingDeletion and PairingMomentRecurrence derive the all-order deletion recurrence from a genuine sigma decomposition and edge-weight factorization; PairingMomentParity proves odd moments zero and empty moments one. The constant-covariance modules now derive actual all-order moments and pairing counts from deletion, prove factorial normalization and a coefficientwise formal exponential identity, and connect these moments to the actual one-variable full polynomial Wick map. The multivariate linear-source modules prove actual assignment/occurrence transport, full Wick linear-power expansion, the pairing endpoint equivalence and assignment-weight factorization, yielding actual Wick moments W_m(h^T C h) and the formal exponential series for symmetric covariance. For rank-one quadratic sources, actual Wick coefficients yield a proved first-order formal ODE, the unique constant-one unit branch, and an exact bridge to the actual matrix determinant det(I+tCA) for A=a h h^T. General full polynomial Wick integration-by-parts is now derived from actual occurrence deletion, Option pairing decomposition and monomial multiplicities, without an assumed IBP identity. The actual mixed-source modules construct finite divided-power coefficients, lift Wick linearly (not as a ring homomorphism), prove polynomial-direction derivatives and insertion identities, and derive both matrix Ward systems with the second-moment covariance term retained. The actual parameter derivative and initial condition are now proved; constant determinant coefficient one yields a genuine matrix unit and two-sided inverse, the actual Ward systems are solved without division by Z, and their substitution gives an actual scalar formal ODE. Full Jacobi, a genuine normalized determinant branch, inverse/source differentiation and first-order formal ODE uniqueness now prove the actual general mixed full-Wick series equals that branch times the formal exponential of the actual quadratic source. The actual even coefficient extraction now has a proved z-graded determinant/exponential formula, vanishing odd coefficients and expand-two reconstruction, with actual inverse/source transport and specialization to the existing doubled tournament block covariance. Actual analytic Taylor arithmetic, finite determinant and genuine inverse transport now identify the existing zero-diamond Gaussian factor Taylor series with the normalized formal determinant branch for v squared equal to one. Actual raw-source and exponential Taylor identities now yield a HasFPowerSeriesAt expansion of the original GaussianSourceProduct.product with the actual descended Wick coefficients for positive n, zero diamonds and v squared equal to one. The actual Wick series now converges to the original product throughout each closed inner disk with radii zero at most r less than R less than pi/2, after one graph-independent order threshold, uniformly quantified over zero-diamond graphs and v squared equal to one without an energy premise. The graph-uniform boundary constant, actual coefficient and weighted l1 estimates, and geometric core Taylor truncation remainder are now instantiated under the explicit linear score-energy bound. A genuine arbitrary-polynomial insertion Ward system and its true-inverse tilted recurrence are proved; their unscaled variable has mean u times response and covariance V. The actual physical-variable scaling, position-deletion recurrence, even-series descent, true-inverse W/eta identification, coefficient minimum-order bounds and permutation invariance are now proved, including repeated labels. These core estimates are not permanent true-tail estimates, and genuine polynomial-valued exponential addition/inversion, residual product factorization, low-order residual cancellation and normalized insertion convolution are now proved at the u-series level. Residual z-descent, frozen finite coefficient identification, logarithmic activity graph expansion and full finite recovery remain separate. Finite polynomial recovery, projection, activities, true tails, permanent recovery and full Condition R remain outside these results. No probability expectation with indefinite covariance is asserted.'),
    }
    (logdir / 'result.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n',
                                       encoding='utf-8')
    print('ALL MODULES PASSED' if result['all_delivered_modules_checked'] else 'VERIFICATION INCOMPLETE')
    return 0 if result['all_delivered_modules_checked'] else 1


if __name__ == '__main__':
    sys.exit(main())
