# ReferenceDiagonal scope

Source supplies exact diagonal row-product formulas for K and T, a unified transitive row-product formula, and adapters from natural-index sums to the entries of Kmatrix² and −Tmatrix².

STATUS: actual Lean 4.35 serial compilation passed. See verification/ReferenceDiagonal.log. Printed dependencies are only propext, Classical.choice and Quot.sound. The actual matrices are explicit, with no square-identity hypothesis.

This module does not establish all-ones orbit identities, negative matrix powers, or Assumption R. Subsequent power comparisons concern nonnegative integer exponents only.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.
