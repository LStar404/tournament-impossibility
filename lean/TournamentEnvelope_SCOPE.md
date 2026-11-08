# TournamentEnvelope scope and current verification status

Source implements:
- `SignMatrix U`: an actual finite real skew matrix with entry absolute value at most 1.
- `ofTournament`: adapter from the existing finite ±1 tournament definition.
- `internal_identity`: exact skew pairing of the selected internal matrix row sum.
- `selected_bound`: true selected-row bound by the complementary vertex sum and half the selected double absolute sum.
- `symmetric_square` / `abs_pair_square`: exact double-sum to triangular pairCost conversion.
- `sum_enumeration`, `sum_enumerated`: canonical increasing finite-subset enumeration.
- `selected_pairCost`: selected double absolute sum is exactly twice the enumerated pairCost.
- `selected_bound_pairCost`: actual matrix selected-row bound with that precise internal pairCost.

The final source has now passed Lean 4.35 compilation, including the enumeration bridge. The log is verification/TournamentEnvelope.log. Printed dependencies are only propext, Classical.choice and Quot.sound, with no sorryAx or added axioms.

This module alone does not establish the final sorted-output weak-majorization statement or Assumption R. It supplies the real-matrix-to-combinatorial-envelope interface for later composition.

Included in the full `verify.py` and `lakefile.toml` build, with raw-entry
independent endpoint audit in `VectorMajorizationEndpoint.lean` and `EndpointCheck.lean`.
