# IteratedVectorMajorization scope

Kernel-checked for arbitrary sequences of actual finite tournament matrices, not merely a fixed matrix:

- trajectory_majorized: the sorted absolute output after r steps is weakly majorized by the r-fold explicit K trajectory of sorted input.
- comparison_cone and comparison_endpoint: every K iterate remains decreasing nonnegative and zero-padded.
- sortedPad_sum_sq: sorting absolute coordinates preserves the actual finite sum of squares.
- trajectory_sum_sq_le and fixed_trajectory_sum_sq_le: squared Euclidean norm bounds against the explicit K trajectory for every natural exponent, including zero.

Actual Lean 4.35 compilation passed. Printed dependencies only propext, Classical.choice and Quot.sound; no sorryAx/new axioms. See verification/IteratedVectorMajorization.log.

This module does NOT identify K's orbit with a transitive matrix orbit and does not prove the final Frobenius comparison against T or Assumption R.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.
