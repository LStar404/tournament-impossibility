# Actual real score energy and ordinary bilinear source

Define the integer score as the row sum of the actual integer sign matrix,
then its real and complex embeddings. Their Euclidean realization is exactly
the existing scoreVector=S1. Its squared Euclidean norm equals the explicit
sum of squared real scores.

For these real-coordinate vectors the Hermitian source is proved equal to
the ordinary bilinear expression b^T M b for any complex matrix M. This is
an exact formal bridge, not an informal identification of two conventions.

For every fixed 0<=R<pi/2, one eventual order threshold works for every
zero-diamond graph and every |w|<=R. Under actual scoreEnergy<=K*n,
the ordinary complex quadratic-resolvent source divided by n² is bounded
by K*C_R²/n, with C_R=2(1+R)exp(R)/cos(R). No graph spectral/operator
smallness assumption remains. Focused Lean checks passed, standard axioms.

This does not yet compose Gaussian parameter substitutions and branches,
source exponentials, fixed derivative errors, permanent recovery, or full R.
Aggregate integration is tracked separately.

Aggregate verification: all 130 delivered modules freshly recompiled PASS
at 2026-11-08T23:50:27.188634Z (zero retained records), all source hashes
match, and the aggregate lake build passed with 9177 jobs.
