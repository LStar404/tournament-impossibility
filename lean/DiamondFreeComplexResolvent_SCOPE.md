# Complex quadratic resolvent: finite algebra and eventual invertibility

Focused Lean compilation passed with only standard logical axioms. For an actual zero-diamond tournament sequence,
this module proves finite and limiting facts for the quadratic matrix A_n(w)=I+(w/n)^2 S_n^2.
It factors A_n exactly as the two linear imaginary-parameter kernels,
identifies its determinant with the square of the finite cosine kernel,
and derives determinant convergence to cos(z)^2 along w_n→z.
Where cos(z) is nonzero it proves eventual left and right inverse identities.

This is not an estimate of the operator norm of A_n inverse. A determinant
lower bound alone does not control inverse norms in growing dimension.
It does not estimate the source quadratic form bᵀ A_n inverse b, establish
an O(1/n) rate, or prove analytic Condition R.

Aggregate verification completed: all 120 modules PASS at
2026-11-08T23:11:24.995047Z, all source hashes match, and lake build passed
with 9167 jobs. This does not enlarge the mathematical scope stated above.
