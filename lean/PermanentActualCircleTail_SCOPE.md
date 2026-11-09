# Actual permanent circle and coefficient tail

The thirteen modules are included in the completed 356-module aggregate verification. The checked build record of 9 November 2026, 22:59 UTC covers 356 Lean modules: 18 exact-source checkpoint records were reused and 338 modules were recompiled. Full Condition R remains unresolved.

`PermanentSpectralFrame.actual_permanent_circle_envelope` bounds the literal permanent of P+zM, with P=J/n. It assumes n>0, nonnegative K,C,T,q, row and column sum norms at most K/n, entry norms at most C/n, Euclidean operator norm at most q, |z|≤T and Tq<1. The bound is (n!/n^n) exp(2TK+(1+TC)sqrt(n)/(1−Tq)). The spectral ordering, moments and circle envelope are derived rather than assumed.

`PermanentActualCircleTail.normalized_actual_tail_bound` turns this into an unweighted absolute coefficient-tail bound beyond floor(δn), for every δ>0 and natural p. After division by n!/n^n the bound is tailConstant(K,C,R,q,δ,p)/n^p, with R>1 and Rq<1. The constant is explicitly defined in the source and independent of n and M within that class.

`BinaryGraphPermanentTail.normalized_tail` instantiates K=2^(r+1)+1, C=1, R=5/4 and q=3/4 for the actual chosen-enumeration positive-depth binary graph branch. Its assumptions are n≥24, an enumeration Bits(r+1)≃Fin(2^(r+1)), a relabeling Fin(n)≃C×Bits(r+1), a real skew base matrix with entries bounded by one, and real |v|≤1. No raw score, operator, moment or circle-bound assumption remains. The cutoff δ and order p are arbitrary within the stated range.

The polynomial is `permanentPolynomial (averaging n) (TournamentSkewMargin.branch ...)`, not a Gaussian core or a formal proxy. The theorem controls the unweighted sum of absolute coefficients in its finite support. It does not prove weighted tail bounds, canonical manuscript popcount identification, core multiplication, activity-window summation, normalized path recovery, projection, the global extremal-structure theorem or full Condition R.
