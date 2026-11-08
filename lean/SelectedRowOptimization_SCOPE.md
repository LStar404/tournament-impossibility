# SelectedRowOptimization scope

`envelope_le_P` combines arbitrary-sign pair-cost optimization with the proved selected-index penalty inequality. The envelope is exactly k(total vector sum − selected vector sum) + internal selected pairCost. It is bounded by the actual tail formula P_k. Selected values are explicitly identified with a strictly increasing finite enumeration of coordinates of x.

This is the optimized combinatorial envelope, NOT yet a theorem about Bx. Missing is the finite enumeration/reindexing proof that the actual tournament signed row sum is bounded by this envelope, followed by identification with the largest k absolute output coordinates and handling general input signs/sorting. The descending/nonnegative hypothesis includes the endpoint coordinate k; the theorem does not require b(k)=0, although zero padding is allowed. No claim of complete vector majorization or R is made.

Actual Lean 4.35 compilation passed; no sorry/admit/new axioms; printed dependencies only propext, Classical.choice, Quot.sound.

Integrated into `lakefile.toml`, full `verify.py`, and `EndpointCheck.lean`;
compiler/axiom output is retained in `verification/SelectedRowOptimization.log`.
