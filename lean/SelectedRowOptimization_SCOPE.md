# SelectedRowOptimization scope

`envelope_le_P` combines arbitrary-sign pair-cost optimization with the proved selected-index penalty inequality. The envelope is exactly k(total vector sum − selected vector sum) + internal selected pairCost. It is bounded by the actual tail formula P_k. Selected values are explicitly identified with a strictly increasing finite enumeration of coordinates of x.

This is the optimized combinatorial envelope, NOT yet a theorem about Bx. Missing is the finite enumeration/reindexing proof that the actual tournament signed row sum is bounded by this envelope, followed by identification with the largest k absolute output coordinates and handling general input signs/sorting. The descending/nonnegative hypothesis includes the endpoint coordinate k; the theorem does not require b(k)=0, although zero padding is allowed. No claim of complete vector majorization or R is made.

Actual Lean 4.35 compilation passed; no sorry/admit/new axioms; printed dependencies only propext, Classical.choice, Quot.sound.

Integrated into `lakefile.toml`, full `verify.py`, and `EndpointCheck.lean`;
compiler/axiom output is retained in `verification/SelectedRowOptimization.log`.

## Subsequent complete finite vector-majorization bridge

TournamentEnvelope, TournamentSwitching, TopAbsoluteSelection and
SelectedTournamentMajorization now construct the actual matrix selected-row
envelope, selected subsets/signs, sorting and signed-permutation bridges, proving
sortedPad(Bx) weakly majorized by K(sortedPad(x)) for every actual finite tournament
and real input. `VectorMajorizationEndpoint.lean` checks the expanded inequality
from raw matrix entries. Earlier exclusions about these particular bridges
above are superseded. Reference K-orbit identities, moment comparisons and R
remain separate, unproved obligations.

## Subsequent concrete reference and moment comparison

The ReferenceMomentComparison dependency chain now discharges the concrete
K-square signed conjugacy, reference column-norm identities and all natural-power
Frobenius comparisons for actual finite tournament matrices. Earlier exclusions
about those interfaces above are superseded by that verified extension.
Exponents are natural numbers (including zero), not arbitrary signed integers.
The all-ones-vector orbit, small-defect sixth-order identity and full R remain
outside these results. See `ReferenceMomentComparison_SCOPE.md`.
