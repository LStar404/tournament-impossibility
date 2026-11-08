# Ordered-block moment recurrence: algebraic layer

`OrdinalMomentRecurrence` defines a packet of four real numbers (size, first
source energy, second source energy, sixth Frobenius moment), together with an
explicit polynomial binary join. It proves three additive invariants and
reconstructs the sixth field of any finite cumulative join as exactly six times
`OrdinalSixthPolynomial.coefficient`.

This module alone is algebra, not a matrix realization. Connecting it to a real
ordered-block matrix requires proofs of ALL THREE binary moment recurrences.
The names of packet fields do not supply those proofs. Empty cumulative input
is included.

The additive invariants are
- alpha = n^3/3 − e,
- beta = f − n^2 e + n^5/5,
- gamma = g/6 − n f − e^2/2 + n^3 e − n^6/6.

This approach avoids a formal log-determinant/series construction, but is
mathematically equivalent at the relevant finite coefficient once the actual
matrix recurrences have been proved.
