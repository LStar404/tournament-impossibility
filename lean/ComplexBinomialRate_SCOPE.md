# Quantitative complex binomial and actual kernel error

For n>0, |w|<=R, R/n<=1/2 and R^2/n<=1, the actual zero-diamond graph
kernel determinant satisfies

    |det(I+i*w*S/n)-cos(w)| <= 2*exp(R)*R^2/n.

The bound is graph-independent and uniform over the whole closed ball.
Every fixed R>=0 eventually satisfies the two size constraints, yielding
O_R(1/n). No radius restriction pi/2 is needed for the determinant itself;
reciprocals need separate zero exclusion.

The proof uses the principal-log remainder on |u|<=1/2 and exp error on
|e|<=1, then the exact finite graph determinant. Focused Lean check and
independent mathematical review passed, standard logical axioms only.
Full aggregate integration is recorded separately.

No inverse matrix norm, source bound, derivative rate, square-root branch,
permanent recovery, or full R follows from this determinant error alone.

Aggregate evidence: 122 modules all PASS at 2026-11-08T23:26:57.226072Z,
using 99 exact-source retained checks plus 23 recompiled checks after fixing
a verifier false-positive on theorem names containing error. Original and
resumed logs are retained. Aggregate lake build passed (9169 jobs).
