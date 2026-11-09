# Actual fixed-depth truncated permanent recovery

This seven-module extension is included in the completed 367-module verification:

1. WeightedFormalExponential
2. ActualCoreTracePrimitive
3. ActualCoreWeightedBound
4. ActivityFiniteWindowBound
5. ActualGraphCoreRecovery
6. PermanentTruncatedRecoveryAlgebra
7. ActualTruncatedPermanentRecovery

## Actual endpoint

`ActualTruncatedPermanentRecovery.actual_permanent_error` bounds the literal
normalized permanent, not a proxy polynomial, by an explicit finite recovery
polynomial. Its assumptions are:

- n≥24;
- fixed positive construction depth d+1;
- a finite real coarse skew matrix B with |B_ij|≤1;
- the supplied graph/vertex enumeration equivalences;
- real v with |v|≤1;
- p≤floor(alpha_d*n);
- complex z with |z|≤1.

Write M=(S+vI)/n for the actual constructed graph branch, and define

    D_d = totalConstant(coordinateConstant d),
    alpha_d = min(log(17/16)/2, 1/(4*exp(1)*D_d)),
    m = floor(alpha_d*n).

The finite polynomial has coefficients

    A_k = sum_{j=0}^p (sum_{a=0}^{p-j} H(k,a)/n^a) * (core M * C_j M)_k

for k≤m and exactly zero coefficients for k>m. Both core and activities are the
pre-existing actual formal objects. The theorem proves

    |per(1+n*z*M)/n! - A(z)| ≤ errorConstant(d,p)/n^(p+1).

The constant is explicit, depends on fixed d and p, and is independent of n, B,
enumerations, v, and z within these hypotheses. Its definition is the sum of
lowConstant, highConstant, and the already proved actual-permanent tailConstant.
The coefficient_error theorem controls the complete coefficient l1 error over
0..n; the difference polynomial vanishes above n. The evaluation theorem follows
on the closed unit disk.

## Proof and boundaries

- The actual core is uniformly bounded at radius 9/8 by
  exp((1025/2)*(2^(d+1)+2)). No diamond-free premise or conclusion is used.
- The old core-conditional positive-activity recovery theorem is instantiated
  with this proved bound in ActualGraphCoreRecovery.positive_order.
- The j=0 product is the core itself. Its nonzero multiplier error is retained.
- For high activities, the proof controls the actual rho-weighted double sum
  sum_j sum_k rho_n(k)*|(core*C_j)_k|, first by the 9/8 coefficient norm, then by
  a finite geometric activity window. It does not substitute a bare-activity
  tail for the recovered tail.
- The low coefficients use the proved exact normalized-permanent = rho*Fk
  identity and the finite projection into core*C_j.
- The high polynomial-degree tail is the old actual normalized-permanent tail,
  because A is exactly zero above m.
- The restriction p≤m is explicit. No unchecked claim about small n or a window
  shorter than p is included. A fixed-order eventual result may later discharge
  this condition using alpha_d>0.
- This is a truncated polynomial result. It does not assert convergence of an
  infinite activity expansion, nor the corresponding estimate for an untruncated
  recovery power series. The later verified extension described in
  WeightedUntruncatedRecovery_SCOPE.md supplies its separate all-k weighted tail
  proof and untruncated endpoint; this note retains the earlier finite theorem.
- The evaluation disk here is |z|≤1. No wider-disk conclusion is claimed.
- This finite truncated theorem is not the full paper raw_fixed_order_recovery
  endpoint. Uniform value error on the closed unit disk alone does not justify
  fixed-order differentiation at the boundary point z=1. The subsequent weighted
  untruncated extension removes the cutoff and proves every fixed k^ell error
  moment, but analytic derivative/evaluation identification remains separate.
  These strengthening steps are outside this seven-module batch.

## Validation

The checked build record of 9 November 2026, 23:31 UTC covers 367 Lean modules: 362 exact-source checkpoint records were reused and 5 modules were recompiled.
Source hashes and printed axiom reports are recorded in verification/result.json.
This aggregate record is distinct from Lake, CI, and publication status.
The theorem remains explicitly finite and truncated, with p<=floor(alpha_d*n)
and |z|<=1; it does not establish the full raw_fixed_order_recovery endpoint
or justify direct boundary differentiation at z=1.
