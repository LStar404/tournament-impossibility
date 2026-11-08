# Explicit finite-order zero-free disk threshold

For 0<=R<pi/2 and |w|<=R, |cos w|>=cos R>0. Using the actual quantitative
finite-kernel error, the finite imaginary kernel has norm at least cos R/2
whenever n>0, R/n<=1/2, R^2/n<=1 and 2exp(R)R^2/n<=cos R/2.
The module also proves that these thresholds hold eventually for each fixed R.
They do not depend on a graph or a parameter w within the disk.

Focused Lean check passed, standard logical axioms only. This is a finite
linear-kernel scalar denominator bound, not by itself a matrix inverse norm
bound, Gaussian branch theorem, or Condition R. Aggregate integration is
tracked separately.

Aggregate verification: all 130 delivered modules freshly recompiled PASS
at 2026-11-08T23:50:27.188634Z (zero retained records), all source hashes
match, and the aggregate lake build passed with 9177 jobs.
