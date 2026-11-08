# TournamentSwitching scope

Actual signed-permutation conjugation of a finite tournament matrix changes arbitrary real input to its sorted absolute coordinates. `Tuple.sort` supplies a genuine permutation; stable tie handling is inherited from Mathlib. The output absolute coordinates are permuted, and sorting the output yields exactly the same sorted absolute vector.

Actual Lean 4.35 compilation passed, including normalized_sorted_output. See verification/TournamentSwitching.log. Printed dependencies are only propext, Classical.choice and Quot.sound, with no sorryAx or added axioms.

This is an algebraic/sorting bridge, not a moment comparison or Assumption R.

Included in the full `verify.py` and `lakefile.toml` build, with raw-entry
independent endpoint audit in `VectorMajorizationEndpoint.lean` and `EndpointCheck.lean`.
