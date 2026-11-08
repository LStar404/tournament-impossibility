# TopAbsoluteSelection scope

An actual Finset is constructed by mapping the first k ranks under the absolute-value sorting permutation. Its cardinality is k, and its signed sum is exactly the largest-k absolute prefix. This supplies a selected row set rather than assuming a maximum is attained.

Actual Lean 4.35 compilation passed; see verification/TopAbsoluteSelection.log. Printed dependencies are only propext, Classical.choice and Quot.sound. It makes no standalone Assumption R claim.

Included in the full `verify.py` and `lakefile.toml` build, with raw-entry
independent endpoint audit in `VectorMajorizationEndpoint.lean` and `EndpointCheck.lean`.
