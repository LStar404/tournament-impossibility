# BasisReference scope

Identifies the actually sorted absolute first basis vector with that same basis vector. This is needed to turn the K comparison trajectory into a concrete first-column matrix-power norm, rather than leaving an unspecified sorted-basis orbit.

Actual Lean 4.35 compilation passed. Log: verification/BasisReference.log. Printed dependencies only propext, Classical.choice and Quot.sound; no sorryAx or added axioms.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.
