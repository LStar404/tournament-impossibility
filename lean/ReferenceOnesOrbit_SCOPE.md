# ReferenceOnesOrbit scope

Actual Lean 4.35 compilation passed.
- Q_ones_shift proves the literal identity Q^T 1 = −J^(floor(n/2)+1)1 in every positive dimension, including n=1.
- reference_vector_norm discharges the generic signed Gram transport assumptions for the actual K/T matrices.
- ones_orbit_norm proves ||K^r 1||² = ||T^r 1||² for every n,r in Nat, including dimension zero and exponent zero.

Logs: verification/reference_ones_orbit.log. Standard three axioms only, no sorryAx or added axioms. Negative or fractional powers and full Assumption R are not asserted.
