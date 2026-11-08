# VectorWeakMajorization: exact scope

Verified using Lean 4.35.0 and this repository's pinned Mathlib.

## Kernel-checked results

* `abel`: the finite summation-by-parts identity, including n=0.
* `weighted_le`: all-prefix inequalities imply inequalities after applying any nonnegative decreasing weight vector.
* `sum_sq_le`: weak majorization of decreasing nonnegative vectors implies the corresponding squared Euclidean norm inequality. The proof uses the weight x+y in `weighted_le`, then cancels the cross terms, avoiding an external convexity or Cauchy theorem.
* `Tournament`: an actual finite real skew sign matrix (off-diagonal entries ±1), with its finite matrix-vector action.
* `Tournament.diagonal`, `edge_bound`, `pair_identity`: actual sign matrix diagonal and edge-level estimates.
* `Tournament.signed_sum_identity`, `signed_sum_bound`: for arbitrary real vectors x,y, twice yᵀBx equals the ordered-pair skew sum and is bounded by the ordered-pair sum of |yᵢxⱼ−yⱼxᵢ|. No hypothetical tournament-limit sequence is substituted for B.

`DescendingNonnegative n x` checks coordinates 0 through n, while prefix sums and squared norms use 0 through n−1. The endpoint can be padded by zero for an ordinary length-n decreasing nonnegative vector. The Abel identity itself holds for any endpoint weight.

## Not proved in this module

The signed selected-row upper bound has NOT yet been optimized to P_k. The balanced-sign prefix counting, order-statistic selected-weight bound, explicit K matrix/cone preservation, signed-permutation sorting, K² reference conjugacy and all-moment iteration remain to be connected/formalized. Thus this module is only finite foundational material for the direct-majorization argument, not a proof of that entire argument, the sixth-moment inequality, or Assumption R.

No `sorry`, `admit`, or added axioms. Printed theorem dependencies are only propext, Classical.choice and Quot.sound. `verification/VectorWeakMajorization.log` records the compiler output.

Integrated into `lakefile.toml`, full `verify.py`, and independent expanded-form
endpoints in `EndpointCheck.lean`. No full selected-row/P_k/K-orbit claim is added.

## Subsequent finite cone and envelope modules

MajorizationCone, SelectedWeight, BalancedSignCounts, SelectedSignPairs and
SelectedRowOptimization now prove K cone/prefix-order preservation and the
optimized combinatorial selected envelope <= P_k. Earlier exclusions above
about these finite ingredients concern this module alone. The actual tournament
matrix-to-envelope interface, output order statistics, signed sorting and
K-reference orbit remain unproved; full vector majorization and R are not claimed.

## Subsequent complete finite vector-majorization bridge

TournamentEnvelope, TournamentSwitching, TopAbsoluteSelection and
SelectedTournamentMajorization now construct the actual matrix selected-row
envelope, selected subsets/signs, sorting and signed-permutation bridges, proving
sortedPad(Bx) weakly majorized by K(sortedPad(x)) for every actual finite tournament
and real input. `VectorMajorizationEndpoint.lean` checks the expanded inequality
from raw matrix entries. Earlier exclusions about these particular bridges
above are superseded. Reference K-orbit identities, moment comparisons and R
remain separate, unproved obligations.
