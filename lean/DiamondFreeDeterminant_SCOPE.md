# Diamond-free principal sign determinants

`DiamondFreeDeterminant.diamondFree_even_principal_det` proves that every even-cardinality principal submatrix of the actual integer sign matrix of a finite `DiamondGap.Tournament` has real determinant one, assuming `DiamondFreeRepresentation.DiamondFree T` (ordinary no-diamond condition). No principal-minor identity is assumed.

Stronger endpoint `diamondFree_det` computes the full determinant as `(1 + (-1)^card V)/2` for all finite diamond-free tournaments, including the empty set. The induced-tournament proof establishes inheritance of diamond-freeness for every principal restriction.

Proof chain:
1. Reuse the already proved transitive-switch and actual finite enumeration.
2. Prove diagonal sign switching preserves the determinant via `D*D=I` (not any path-count invariance).
3. Reuse the author's original exact transitive-kernel determinant formula; derive the homogeneous formula for `det(aI+S)` for nonzero real `a`, then extend by continuity to `a=0`.
4. Reindex by the actual enumeration; restrict to the requested vertex subset.

`TournamentHamiltonian/TransitiveDeterminant.lean` is copied unchanged from public author repository `LStar404/tournament-hamiltonian-paths`, commit `6144fe396da98debdf31baa10fd7388312189d9f`. Both modules were actually compiled on Lean 4.35.0 with the current pinned mathlib. No `sorry`, `admit`, or custom mathematical axiom was introduced. This batch by itself is a determinant theorem, not the permanent expansion or full R.
