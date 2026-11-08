# ReferenceMomentComparison: verified all-natural-power comparison

## Exact theorems

- reference_column_norm: for the actual explicit K and T matrices, every column of K^r has exactly the same squared norm as its signed-zigzag-corresponding column of T^r, for every natural r.
- comparison_basis_norm: the actual K trajectory used in finite vector majorization is identified with the first-column norm of the actual transitive matrix power.
- frobenius_all_powers: for every natural dimension n, every natural exponent r, and every real finite tournament sign matrix B,

      sum(i,j) ((B^r) i j)^2 ≤ sum(i,j) ((T_n^r) i j)^2.

Dimensions and exponents zero are included. Matrix powers are genuine Matrix multiplication, not pointwise powers.

## Discharged interfaces

The final theorem assumes only an actual tournament. The proof supplies rather than postulates:
1. finite vector majorization and its K iteration;
2. P-difference K = the explicit signed anti-diagonal matrix;
3. the genuine zigzag permutation and signs;
4. K²=Q(−T²)Qᵀ and Q orthogonality;
5. symmetric/skew-symmetric normality and Gram-power transport;
6. the basis-vector sorting identity;
7. signed cyclic symmetry of T and equality of all its power-column norms.

In particular, the generic SignedConjugacy lemma's Gram-relation hypothesis is discharged by the concrete reference proof; it is not a hidden hypothesis of frobenius_all_powers.

## Verification

Actual serial Lean 4.35.0 compilation passed. Both printed final theorem dependencies are only propext, Classical.choice and Quot.sound, with no sorryAx or added axioms. Main log: verification/ReferenceMomentComparison.log. The separate ReferenceMomentEndpoint.lean takes raw Matrix entries and only skew/±1 hypotheses; its log records an independent expanded endpoint check.

## Limits

Only nonnegative integer powers are asserted, not negative or fractional powers. No uniqueness of maximizing matrices is asserted. This module does not prove the separate all-ones-vector orbit identity, the small-defect sixth-order identity, infinite spectral/asymptotic consequences, or full Assumption R. These remain distinct tasks.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.

## Subsequent all-ones and source-energy result

ReferenceOnesOrbit now proves the actual all-ones reference orbit. TournamentEnergyRowDomain proves convergence and source-energy series comparison for real q≥0 with q*(n−1)²<1 (truncated natural n−1), including q=1/n² for n>0 without a summability premise. These later modules supersede the corresponding earlier exclusions, but do not identify a resolvent or establish small-defect sixth-order identities or Condition R.
