# ReferenceSquare scope

Verified arbitrary-size finite summation identities for explicit reference matrices:
- Kentry is the anti-diagonal zero matrix with 1 above the anti-diagonal and alternating ±1 below it.
- Tentry is the transitive tournament sign matrix.
- sum_two_breaks splits the finite row-product sum exactly at the two exceptional zero coordinates.
- T_row_dot_offdiag gives n−2(j−i) for i<j<n.
- K_row_dot_offdiag gives (n−1−j)+the alternating middle-block sum+i*alt(j−i).

These are actual sum identities, not finite-size experiments. Lean 4.35 compilation passed and the two main theorem axiom prints contain only propext, Classical.choice and Quot.sound. See verification/ReferenceSquare.log.

Diagonal identities, signed zigzag conjugacy and the connection to the P-difference operator are supplied by separate modules. This module alone is not an all-moment comparison or proof of Assumption R.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.
