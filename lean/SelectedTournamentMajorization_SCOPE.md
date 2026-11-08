# SelectedTournamentMajorization: verified finite vector comparison

## Exact result

For every finite real matrix B with skew symmetry and off-diagonal entries ±1, and every real input x, the theorem `tournament_vector_majorization` proves

    sortedPad(B x) ≺_w K(sortedPad x).

`sortedPad` is the actual absolute-coordinate sort using Mathlib's tuple permutation, followed by zero extension. `K` is the explicit P-difference operator from MajorizationCone. The expanded `tournament_prefix_bound` states every prefix bound directly as

    sum(top k |Bx|) ≤ k sum(|x|) − sum(j<k) (1+2 floor(j/2)) x*(n−k+j).

There is no assumed comparison inequality or assumed limiting/extremal tournament sequence. The selected subset, its increasing enumeration, the optimizing signs, and the input/output sorting permutations are constructed in the proofs. Empty dimensions and zero-length selections are included.

## Verification

All four new bridge modules compiled serially under Lean 4.35.0 and the pinned Mathlib. Final theorem axiom output contains only propext, Classical.choice and Quot.sound, with no sorryAx or added axioms. Main log: verification/SelectedTournamentMajorization.log.

The independent expanded check VectorMajorizationEndpoint.lean takes raw entries A, skew and ±1 hypotheses, and expands matrix-vector multiplication into an actual finite sum. Its result does not hide the target inequality inside a structure hypothesis. See verification/VectorMajorizationEndpoint.log for the separate check.

## Remaining boundary

This closes the finite selected-row/vector weak-majorization bridge and composes with the already verified K cone/prefix-order preservation. It does NOT prove the alternate anti-diagonal matrix representation of K, K² signed-permutation conjugacy to −T², reference-orbit norm identities, all-moment Frobenius comparison, the later sixth-deficit/asymptotic interfaces, or Assumption R. These must not be claimed as consequences already formalized by this module.

Included in the full `verify.py` and `lakefile.toml` build, with raw-entry
independent endpoint audit in `VectorMajorizationEndpoint.lean` and `EndpointCheck.lean`.

## Subsequent concrete reference and moment comparison

The ReferenceMomentComparison dependency chain now discharges the concrete
K-square signed conjugacy, reference column-norm identities and all natural-power
Frobenius comparisons for actual finite tournament matrices. Earlier exclusions
about those interfaces above are superseded by that verified extension.
Exponents are natural numbers (including zero), not arbitrary signed integers.
The all-ones-vector orbit, small-defect sixth-order identity and full R remain
outside these results. See `ReferenceMomentComparison_SCOPE.md`.
