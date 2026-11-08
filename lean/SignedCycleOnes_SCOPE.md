# SignedCycleOnes: verified signed cyclic all-one orbit

The module uses the actual negative cyclic matrix J and actual transitive T from TransitiveOrbit, without changing that frozen module.

Verified under Lean 4.35.0:
- `J_power_ones d k (k≤d+1)`: J^k applied to the all-one vector is exactly the step vector with its first k coordinates −1 and all remaining coordinates +1. The endpoint k=d+1 is included, including dimension 1 and k=1.
- `J_power_sum_sq`: every nonnegative integer power J^k preserves the finite sum of squared coordinates for arbitrary real vectors.
- `powers_commute`: T^r and J^k commute for all nonnegative integer exponents.
- `transitive_shift_sum_sq`: the squared norm of the T^r orbit is unchanged under an arbitrary J^k shift of the input.
- `transitive_step_sum_sq`: the explicit negative-prefix step vector and the all-one vector have equal T^r orbit squared norm, whenever k is in [0,d+1].

The actual compilation log is verification/signed_cycle_ones.log. All printed endpoints depend only on propext, Classical.choice and Quot.sound. No sorry/admit/new axioms.

Boundary: Qᵀ1's identification with the negative of this step vector, and the K/T all-one reference norm equality, are composition steps in other modules. This module alone is not Assumption R.
