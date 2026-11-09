# Fixed-order weighted untruncated actual recovery

These four modules are included in the completed 367-module verification:

1. WeightedRecoveryMultiplier
2. RecoveryMomentTail
3. WeightedRecoveryClosure
4. ActualWeightedUntruncatedRecovery

## Quantified actual endpoint

Fix d,p,ell in Nat. The graph construction depth is d+1. For every n≥24, finite
coarse index type, real skew coarse matrix B with |B_ij|≤1, the required graph
and vertex enumeration equivalences, and real v with |v|≤1, set

    M = TournamentSkewMargin.branch (realGraph (d+1) e B f) v,
    D_d = ActualGraphCoreRecovery.activityConstant d,
    alpha_d = min(log(17/16)/2, 1/(4*exp(1)*D_d)).

The remaining explicit order/window condition is p≤floor(alpha_d*n). There is
no additional ell-dependent dimension threshold. Constants may depend on d,p,
ell; no uniformity in growing depth or derivative order is asserted.

Let P be the previously verified actual normalized permanent polynomial and U
be RecoveryMomentTail.untruncated M p. Its kth coefficient is exactly

    sum_{j=0}^p sum_{a=0}^{p-j}
        (H(k,a)/n^a) * (actualCore M * actualActivity M j)_k.

The (j,a) summation is finite; k is no longer truncated.

ActualWeightedUntruncatedRecovery.coefficient_error proves

    Summable (k ↦ k^ell * |P_k-U_k|)
    and sum_k k^ell * |P_k-U_k|
        ≤ errorConstant(d,p,ell)/n^(p+1).

The constant is defined explicitly and is independent of n, B, enumerations,
and v within the stated class. weighted_summable separately gives absolute
summability of every fixed moment of U itself. No divergent tsum is accepted
as a norm bound.

## Proof components

- Low activities use the true factorial-ratio remainder with moment exponent
  2*(p-j+1)+ell. The j=0 core contribution is retained.
- High activities retain the actual rho weighting. A moment factor
  moment(17/18,ell) multiplies the proved finite activity-window estimate.
- The actual permanent's high-degree weighted tail uses its independently
  proved unweighted tail at order p+ell+1 and the exact degree bound k≤n.
  Thus k^ell≤n^ell costs no net inverse-power order.
- The approximant tail is a finite sum over (j,a). For q=p+1-j-a>0 and
  k>floor(alpha_d*n), absorb (alpha_d*n)^q into k^q. The exponent
  2*a+ell+q is controlled by moment(8/9,2*a+ell+q). The exact denominator
  identity is a+q+j=p+1.
- The global theorem controls every finite coefficient subset before deriving
  Summable and the tsum bound. It is not only a low-degree window estimate.

## Derivative interface and explicit exclusions

ActualWeightedUntruncatedRecovery.derivative_coefficients_at_one proves
summability and an error bound for the falling-factorial coefficient sums

    sum_k (k)_ell * P_k   and   sum_k (k)_ell * U_k.

This is a derivative-ready interface at z=1, not a completed analytic
iteratedDeriv identification for the evaluation function of U. That analytic
bridge remains a separate task. The polynomial side and power-series side must
both be identified correctly before presenting this as an analytic derivative
theorem. No new larger-disk analytic theorem is claimed by this batch.

This is the actual fixed-depth graph specialization. It does not prove the
upstream raw_fixed_order_recovery theorem for every matrix satisfying abstract
C,K,q assumptions and every radius r<1/q. Nor does it prove infinite activity
convergence, a uniform-in-depth estimate, an edit-Lipschitz remainder, the
extremal entrance theorem, or the full R chain. No diamonds=0 condition is
inferred or used.

## Validation ownership

The checked build record of 9 November 2026, 23:31 UTC covers 367 Lean modules: 362 exact-source checkpoint records were reused and 5 modules were recompiled.
Source hashes and printed axiom reports are recorded in verification/result.json.
This aggregate record is distinct from Lake, CI, and publication status.
The all-k weighted untruncated coefficient estimate and falling-factorial interface
are proved; analytic iteratedDeriv identification and full Condition R remain open.
