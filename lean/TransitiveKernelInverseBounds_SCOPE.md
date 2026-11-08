# Explicit entry bounds and genuine Euclidean inverse norm

Focused Lean checks prove the following for the actual inverse of the existing
positive-above-diagonal transitive kernel I+aT, of size n=m+1>=1.
Assume |a|<=R/n and 0<c<=|H_n(a)|, where H_n(a)=((1+a)^n+(1-a)^n)/2.
The assumptions imply R>=0 automatically.

* The explicit numerator has diagonal norm <=(1+|a|)^(n-1).
* Its off-diagonal norm is <=|a|(1+|a|)^(n-2). The factor |a| is retained.
* Thus inverse diagonal entries have norm <=exp(R)/c and off-diagonal entries
  have norm <=R exp(R)/(n c).
* The true Euclidean operator norm of the matrix inverse is

      ||toEuclideanCLM ((I+aT)^(-1))|| <= (1+R)exp(R)/c.

The operator result is derived, not assumed. The proof separates the scalar
identity part dI, then applies the verified Frobenius-to-Euclidean bridge only
to the O(1/n) off-diagonal remainder. It does not infer an inverse norm from a
determinant lower bound alone, and it does not apply a Frobenius estimate to
the full inverse (which would introduce a spurious sqrt(n) loss).

Focused compilation exits 0. The three exported axiom reports contain only
propext, Classical.choice, Quot.sound. The dependency TransitiveKernelInverse
was also recompiled to its library .olean. Aggregate integration and publication
are separate steps owned by the parent task.

This module does not itself transfer the estimate to arbitrary zero-diamond
tournaments, discharge the scalar denominator lower bound uniformly on a
disk, prove source estimates, or establish full Condition R.

Aggregate verification: all 130 delivered modules freshly recompiled PASS
at 2026-11-08T23:50:27.188634Z (zero retained records), all source hashes
match, and the aggregate lake build passed with 9177 jobs.
