# Actual zero-diamond kernel inverse operator bound

For n>0, actual zero diamond count, |a|<=R/n, c>0 and |H_n(a)|>=c,
the actual graph inverse satisfies the true Euclidean operator norm bound

    ||(I+aS)^-1|| <= (1+R)*exp(R)/c.

No spectral or operator-norm smallness is assumed. The proof transfers exact
transitive inverse entries by genuine sign switching and vertex relabeling,
identifies the diagonal with one scalar, and controls the remaining entries
by R exp(R)/(n c). Only the error part receives a Frobenius estimate.

A determinant lower bound alone would not suffice in growing dimension;
this module crucially uses the verified inverse-entry formula. The fixed-disk
application subsequently supplies the denominator bound rather than assuming
it. Focused Lean check passed; aggregate verification is recorded separately.

Aggregate verification: all 130 delivered modules freshly recompiled PASS
at 2026-11-08T23:50:27.188634Z (zero retained records), all source hashes
match, and the aggregate lake build passed with 9177 jobs.
