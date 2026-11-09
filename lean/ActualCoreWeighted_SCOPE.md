# Actual core weighted bound

Three modules in the completed 363-module verification:

1. WeightedFormalExponential
2. ActualCoreTracePrimitive
3. ActualCoreWeightedBound

The mathematical endpoint is `ActualCoreWeightedBound.graph`. For n≥24,
fixed construction depth depth+1, every real skew coarse matrix with entries
bounded by 1, the supplied graph enumerations, and real |v|≤1, the original
`ActualResidualFrozenFactorization.core M` has finite weighted coefficient norm
at radius 9/8 and norm at most

    exp((1025/2)*(2^(depth+1)+2)).

The bound is independent of n and the coarse matrix but depends on depth.
It is not a claim for growing depth, complex v, or unrestricted matrices.
There is no diamond-free assumption or conclusion, and no external core norm,
inverse, or analytic estimate premise in this graph endpoint.

The proof identifies the old canonical determinant branch using a formal trace
primitive and Jacobi's identity. The source is exactly half the sum of the old
physical means. A generic weighted formal-exponential bound uses only finite
truncations, bounded partial coefficient sums, and the existing algebra norm.

The previous conditional core-activity recovery lemmas can now be instantiated
with `ActualCoreWeightedBound.graph` and `coreConstant depth`. Finite summation of the growing activity window and final truncated recovery
assembly are handled by the additional modules listed in
ActualTruncatedRecovery_SCOPE.md. Neither endpoint asserts infinite activity
convergence.

## Verification record

The checked build record of 9 November 2026, 23:23 UTC covers 363 Lean modules: 275 exact-source checkpoint records were reused and 88 modules were recompiled.
This record does not certify a Lake build, CI, or publication. The fixed-depth
actual-core norm is proved; untruncated recovery, the required boundary
derivative passage, and full Condition R are not proved by this extension.
