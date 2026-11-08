# TransitiveOrbit: verified reference-matrix orbit symmetry

## Definitions

`T n` is the actual n×n real transitive tournament sign matrix: +1 above the diagonal, −1 below, and 0 on the diagonal. `transitiveTournament n` explicitly verifies the earlier actual-tournament structure.

For positive dimension n=m+1, `J m` is the signed cyclic shift whose jth column is epsilon(j)e_(finRotate j), where epsilon is −1 only at the last index. Thus J sends e_i to e_(i+1) before the boundary and e_last to −e_0.

## Kernel-checked results

- `T_covariant`: exact signed cyclic covariance of the actual T entries.
- `T_commutes_J`: the actual matrix identity T J = J T.
- `mul_covariant`, `power_covariant`: the covariance is inherited by products and all nonnegative integer powers.
- `power_columns_equal`, `power_columns_eq`: every column of every integer power T^r has exactly the same sum of squared entries. The dimension-uniform theorem includes n=0 vacuously.
- `power_frobenius`: the Frobenius square of T^r equals n times the squared norm of its first column for positive dimension.

Lean 4.35 compilation succeeded on the first complete run. The log `verification/TransitiveOrbit.log` prints only propext, Classical.choice and Quot.sound for all principal endpoints. No sorry/admit/new axioms.

## Boundary

This proves the transitive reference orbit symmetry. It does not itself prove the K² signed-permutation conjugacy, equality of K and T reference-orbit norms, arbitrary-tournament moment domination, or Assumption R. These remain separate composition steps.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.
