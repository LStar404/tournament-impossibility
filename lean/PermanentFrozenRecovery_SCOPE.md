# Exact normalization and conditional core-activity recovery

This batch connects the literal normalized permanent polynomial to the previously
defined finite pairing coefficients. It does not assume that coefficient bridge.

For n > 0 and a complex n-by-n matrix M, define

f_M(z) = (n^n/n!) per(J/n + z M) = per(J + n z M)/n!.

For every natural k with k <= n, the new theorem proves

coeff_k(f_M) = (n^k/(n)_k) Fk(M).

Fk retains the earlier subset-pairing definition. The proof counts exactly
(n-k)! completions of each selected minor, connects its bijection sum with the
existing pairing weight, and handles the row/column indexing swap explicitly.
For k > n both the actual coefficient and Fk are separately proved zero. The
empty-matrix normalized polynomial is separately proved to be 1.

The finite residual/activity identity is then connected to the same polynomial:
for n > 0 and k <= min(m,n), its coefficient is the actual factorial multiplier
times the kth coefficient of the finite sum over j <= m of core(M) Cj(M).
The finite projection identity for Fk itself holds for every k <= m.
Terms with j > k vanish. No infinite activity sum or convergence assertion is used here.

The exact normalized polynomial is also the object controlled by the genuine
positive-depth binary-graph permanent tail theorem. Its scalar normalization,
coefficient norms, support, and polynomial evaluation are explicitly identified.
This tail endpoint is for the unweighted coefficient tail, at every positive
linear cutoff and every fixed inverse-power order.

For core-times-activity factorial recovery, the batch proves the correct
n^(-p-1) finite-window error for each j <= p from an explicit weighted coefficient
norm bound on the actual core. The positive-activity graph endpoint discharges
the old activity estimates internally. The core bound remains a premise.
The j=0 summand is the core itself, not the constant series, and its recovery
error is retained rather than incorrectly set to zero.

## Limits

- The previous diamond-free core norm theorem still requires an actual
  diamond-free tournament, its energy bound, and the branches v^2=1. It has not
  been extended to arbitrary coarse graphs in the positive-depth family.
- The actual graph endpoint remains stated for the chosen finite enumeration;
  it does not identify the manuscript's canonical popcount numbering.
- This batch does not sum the complete fixed-order recovery error, establish
  the depth-dependent activity cutoff, or bound the finite-order approximant's
  coefficient tail. The separate ActivityLinearWindowSum draft is not included.
- A weighted true-tail theorem at arbitrary radius greater than 1 is not claimed
  by the unweighted tail endpoint.
- Full normalized fixed-order recovery, structural projection, classification,
  and Condition R remain unproved by this batch.

## Modules

1. PermanentSubsetMinorBridge
2. CoreActivityFactorialBridge
3. PermanentFrozenCoefficientExpansion
4. PermanentRestrictionFiber
5. PermanentFrozenCoefficientBridge
6. PermanentNormalizedFrozenBridge
7. CoreActivityFiniteProjection
8. PermanentNormalizedTailBridge
9. PermanentCoreFiniteRecovery

These nine modules are included in the completed 356-module aggregate verification.
The checked build record of 9 November 2026, 22:59 UTC covers 356 Lean modules: 18 exact-source checkpoint records were reused and 338 modules were recompiled.
This record does not itself certify a Lake build or publication. The actual-core
uniform norm remains a premise, and full Condition R remains unproved.
