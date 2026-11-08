# Actual zero-diamond kernel limits

`DiamondFreeKernelLimit` proves genuine limits for a family of actual
zero-diamond tournaments of every finite order. The graph at each order can
be chosen independently; no shared labeling or switching choice is assumed.

For any complex parameter sequence w_n converging to z:

* det(I + (w_n/n) S_n) converges to cosh z;
* det(I + (i w_n/n) S_n) converges to cos z;
* when cos z is nonzero, the reciprocal determinant converges to 1/cos z;
* the imaginary-parameter matrix eventually has a genuine two-sided inverse.

The last statement explicitly proves both products with the inverse are I;
it does not confuse the totalized Lean inverse of a singular matrix with an
actual inverse. The finite n=0 convention has no effect on these limits.

Focused compilation passed; printed axiom reports use only propext,
Classical.choice, Quot.sound. Aggregate integration is recorded below.

These theorems do not claim an O(1/n) rate, uniform convergence on disks,
an operator-norm bound for a matrix inverse, source-energy control, analytic
branches, derivative convergence, permanent recovery, or full Condition R.
Any subsequently verified compact-uniform theorem will be a distinct module.

Aggregate verification completed: all 120 modules PASS at
2026-11-08T23:11:24.995047Z, all source hashes match, and lake build passed
with 9167 jobs. This does not enlarge the mathematical scope stated above.
