# Ordinal sixth coefficient polynomial: exact scope

This module proves a **finite real-polynomial identity**, not yet an actual
ordinal-sum matrix sixth-moment identity. The definition `coefficient` is the
right-hand side of (★) in `ordinal_sixth_deficit_determinant_proof.md`.

## Proved

- Reference cubic aggregate is n/3, and replacing e0 by e0−8t shifts it by 8∑t.
- Exact subtraction of two explicitly defined coefficient polynomials, with
  arbitrary real arrays m, f0, g0, Q, L, t and ∑m=n.
- The interaction term is exactly −384∑_{j<i}t_j t_i; pair enumeration and the
  square-of-sum identity are proved, including k=0.
- Factorization of n³−3nm²+2m³−n+m and interaction upper bound by (∑t)²/2.
- If n≥0 and 0≤h≤n/2, the scalar bracket is at least 6n³−16n.
- If n≥4, r≥0, D≤(n−3)r, and the prior delta lower bound is GIVEN, then
  delta≥6n²D. These graph-specific assumptions remain explicit.

## Not proved by this module

- That `coefficient` equals [z⁶]log det(I−zS) for actual ordinal-sum S.
- The ordinal block determinant formula or its formal-power-series extraction.
- Identification e0−e=8t with the actual cyclic triangle count.
- Graph-specific estimates relating block sizes, triangles, diamonds, and r.
- The actual sixth-moment deficit formula, small-diamond spectral bound, or R.

Do not advertise the polynomial or conditional scalar endpoint as a completed
matrix/spectral theorem. Previously proved actual all-natural-power moment
comparison is a separate result and does not close this missing bridge.

## Verification

`OrdinalSixthPolynomial.lean` compiled serially using pinned Lean 4.35.0/Mathlib.
Independent `verification/OrdinalSixthPolynomialEndpoint.lean` expands all
coefficient definitions and the pair sum. Audit the corresponding verification
logs. No new axioms, sorry, or admits are introduced.

## Subsequent actual matrix bridge

OrdinalSixthMatrixBridge now proves that 6 times this coefficient polynomial equals the actual squared Frobenius norm of the cube of the ordered block matrix, for all finite families of real skew blocks, via proved two-block recurrences. No determinant identity is assumed. This closes the actual sixth-moment identification but does not establish triangle-count identities, small-diamond counting estimates or R.
