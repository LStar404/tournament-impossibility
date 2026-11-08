# Genuine complex operator and source bounds

For a bounded operator A on a complete complex inner-product space, retain
the explicit hypothesis |w|^2*||A||^2 <= q < 1. The norm here is the genuine
ContinuousLinearMap operator norm, not an entrywise matrix norm.

The Neumann series is proved to be the two-sided inverse of I+w^2*A^2,
with norm <=1/(1-q). Cauchy--Schwarz gives
|<b,Rb>| <= ||b||^2/(1-q). If n>0 and ||b||^2<=K*n, the normalized quantity
|<b,Rb>|/n^2 <= K/(n*(1-q)).

Focused compilation passed, standard logical axioms only. Aggregate
integration is recorded separately. The operator smallness and energy
hypotheses have NOT been discharged for the actual graph families in the
enlarged complex disk. This reusable analytic interface must not be called
the complete graph source theorem. No determinant lower bound is used as
a substitute for an operator-norm bound.

Aggregate evidence: 122 modules all PASS at 2026-11-08T23:26:57.226072Z,
using 99 exact-source retained checks plus 23 recompiled checks after fixing
a verifier false-positive on theorem names containing error. Original and
resumed logs are retained. Aggregate lake build passed (9169 jobs).
