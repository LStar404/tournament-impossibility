# Actual Gram spectral frame

Focused Lean verification passed. Constructs the actual positive Gram matrix AᴴA, its library eigenvector unitary, nonnegative eigenvalues, square/fourth roots and concrete factors X=AVdiag(d^-1), Y=Vdiag(d). Proves the spectral representation and that a zero Gram eigenvalue annihilates the corresponding actual column under A. No diagonalization or kernel premise is assumed.

PermanentSpectralFactors completes the exact factorization. These modules do not prove a permanent inequality, positive moment representation, circle envelope or true permanent tail.
