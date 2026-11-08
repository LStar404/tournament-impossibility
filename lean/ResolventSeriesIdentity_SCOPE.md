# ResolventSeriesIdentity: verified generic matrix-series identification

Actual serial Lean 4.35.0 compilation passed.

Verified statements:
- inverse_eq_geometric: summable powers of an actual real finite matrix C give the genuine matrix inverse (1−C)⁻¹ = Σ C^r.
- inverse_left_right: both inverse multiplication identities hold. This rules out reliance on the totalized singular-matrix fallback of the inverse definition.
- quadratic_hasSum and quadratic_resolvent_eq_tsum: the inverse quadratic form equals the sum of the actual quadratic coefficients, proved by entrywise HasSum and two finite sums.
- source_coefficient: for a normal real matrix A, C=q(AᵀA) and b=A1, each coefficient equals q^r||A^(r+1)1||². The coefficient identity is proved, not assumed.
- source_resolvent_eq_series: the resulting source resolvent quadratic equals its energy series.

Summability and normality are EXPLICIT assumptions in this generic module. The concrete tournament application must discharge them using the actual matrix and numerical domain. This module alone does not claim a tournament convergence domain, a comparison theorem, an optimal/complex spectral domain, differentiated inequalities, a sixth-defect identity, or full Assumption R.

Log: verification/resolvent_series_identity.log. Printed endpoint dependencies are only propext, Classical.choice and Quot.sound, with no sorryAx or added axioms. Source and olean are frozen.
