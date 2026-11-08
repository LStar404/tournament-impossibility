# KMatrixIdentification scope

Actual Lean 4.35 compilation passed.
- coefficient_entry proves the P-difference coefficients equal ReferenceSquare.Kentry, the explicit symmetric signed anti-diagonal matrix.
- K_action identifies the previously proved operator K with actual matrix-vector multiplication.
- comparison_power identifies every K iteration with an actual matrix power acting on the finite input.

Thus this module closes the representation interface rather than postulating it. It does not itself prove a K/T orbit comparison. Log: verification/KMatrixIdentification.log; standard three axioms only.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.
