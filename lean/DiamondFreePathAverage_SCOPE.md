# Zero-diamond two-permanent identity: exact finite scope

## New modules

1. `TournamentHamiltonian/TransitiveDeterminant.lean`: copied unchanged from the author's old repository, commit `6144fe396da98debdf31baa10fd7388312189d9f`.
2. `DiamondFreeDeterminant.lean`: actual zero-diamond sign matrices have determinant `(1+(-1)^N)/2`; every even principal minor has determinant one. Uses the existing source-switch construction and actual transitive enumeration. Sign switching is used only for determinants, never asserted to preserve Hamiltonian paths.
3. `PermanentDiagonalExpansion.lean`: arbitrary real square matrix A and real v satisfy
   `per(A+diag(v)) = Σ_U v^|U| per(A[Uᶜ])`.
   Proves the actual permutation/subset expansion, including empty matrices, through a bijection between permutations fixing the removed set and permutations on its complement. Averaging v=+1,-1 selects even U.
4. `DiamondFreePathAverage.lean`: explicitly converts the same Boolean tournament to its integer sign matrix, then combines the two preceding facts with the previously proved S1 convolution.

## Endpoints and exact hypotheses

- `TournamentHamiltonian.diamondFree_sign_principal_det`: actual Boolean tournament, ordinary diamond absence, even selected set.
- `TournamentHamiltonian.diamondFree_normalized_path_two_permanents`: positive order `n+1`, ordinary diamond absence. Proves the exact normalized expression with denominator `2*(n+1)!`.
- `NonAlgebraicity.zero_diamonds_hamiltonianPathCount_two_permanents`: the existing main-paper `Orientation` and `hamiltonianPathCount`, with hypothesis literally `diamonds.card = 0` for its exact sign encoding.

The resulting equation is
`2^n H/(n+1)! = (per(J+S+I)+per(J+S−I))/(2*(n+1)!)`.
No principal-minor assumption, permanent expansion assumption, path-convolution assumption, classification assumption, or asymptotic input is present in the endpoint. The theorem applies to the original tournament, not a switched graph. The positive-order parameterization handles n=1 correctly; determinant/permanent expansion lemmas also cover the empty matrix.

## Limits

This proves the finite S1 two-branch identity, not R, asymptotic permanent recovery, extremal classification, or any remaining nonlocal estimates. It does not say ordinary sign switching preserves the path count. Whole-project build/integration is separately owned by the integrator.

## Validation

All four new modules were actually compiled in the current Lean 4.35.0 pinned-mathlib environment. The final compile plus independent `#print axioms` process exited 0. Checks of `permanent_add_diagonal_complement`, `permanent_two_branch_average`, `diamondFree_even_principal_det`, and `zero_diamonds_hamiltonianPathCount_two_permanents` all reported exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, or custom axioms appear in these source files. Repository-wide validation and publication are separate integration steps, not claimed by this module-level check.
