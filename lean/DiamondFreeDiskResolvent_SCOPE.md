# Actual zero-diamond complex disk resolvent and source bounds

Focused Lean compilation passed and generated the library .olean. All five
exported axiom reports contain only propext, Classical.choice, Quot.sound.
Aggregate integration and publication are separate parent-owned steps.

For n>0, an actual zero-diamond tournament T, 0<=R<pi/2 and |w|<=R, assume
only the explicit finite-order thresholds

  R/n <= 1/2,
  R^2/n <= 1,
  2 exp(R) R^2/n <= cos(R)/2.

Define C_R=(1+R)exp(R)/(cos(R)/2). This module proves:

* Both linear imaginary-parameter kernel inverses have genuine Euclidean
  operator norm <=C_R, using the verified explicit inverse-entry formula and
  the concrete scalar denominator lower bound.
* The actual quadratic matrix I+(w/n)^2 S^2 has a true two-sided inverse.
* Its actual inverse has Euclidean operator norm <=C_R^2, not just a scalar
  determinant estimate.
* For any complex Euclidean vector b, the Hermitian source form is bounded by
  ||b||^2 C_R^2. If ||b||^2<=K n, its normalization by n^2 is <=K C_R^2/n.
* `scoreVector T` is the actual complex embedding of S times the all-ones
  vector, and the normalized source theorem is instantiated at this vector.

`eventually_uniform_resolvent` and `eventually_uniform_source` discharge
existence of the order threshold using ComplexKernelDiskLower.eventually_thresholds.
The threshold works simultaneously for ALL zero-diamond tournaments at that
order, ALL complex parameters in the closed disk, and in the source theorem
ALL vectors and energy constants meeting the stated energy inequality.

There is no spectral-bound or operator-norm hypothesis in these endpoints.
The linear-energy premise remains an explicit, substantive assumption on b;
zero-diamond status alone does not imply it. The endpoint uses the Hermitian source. Identifying it formally with the
original transpose-based source requires the separate real-score bridge; this
module does not claim that bridge has already been proved.

Not included: square-root/log branch estimates for k_n and beta_n, the complete
Gaussian prefactor bound, derivative/Cauchy estimates, common-projection
independence, permanent recovery, nonzero-core analysis or full Condition R.

Aggregate verification: all 130 delivered modules freshly recompiled PASS
at 2026-11-08T23:50:27.188634Z (zero retained records), all source hashes
match, and the aggregate lake build passed with 9177 jobs.

The separate ActualComplexScoreSource module in this batch now supplies the
exact real-score energy and ordinary-transpose source bridge noted above.
