# Actual mixed-source formal coefficients and both Ward systems

Seven modules extend the proved full polynomial Wick IBP. Coefficients lie in a characteristic-zero field S; labels are finite. Covariance K and interaction A are symmetric bilinear matrices, not Hermitian.

* `FormalLinearLift`: coefficientwise lift of a linear functional, with compatibility with scalar-series multiplication. It is intentionally not a ring homomorphism.
* `FormalDividedPowers`: actual coefficients R^n/n!, actual coefficientwise derivation, Leibniz rule and the polynomial-direction derivative of the exponential series.
* `FormalMixedExponential`: defines E=exp(u L) exp(u² H) as a product of actual divided-power series and expand2. Proves the finite Cauchy coefficient formula and polynomial-direction derivative, rather than assuming a desired exponential equation.
* `MixedSourcePolynomials`: L=sum h_i X_i and H=−(1/2)sum A_ij X_i X_j; computes their actual partial derivatives, using symmetry of A for H.
* `FormalWickInsertion`: defines moments with actual polynomial insertions and proves coefficientwise insertion IBP using the previously verified full Wick functional.
* `ActualMixedSourceWard`: defines actual Z=W(E), G_i=W(X_i E), H_ij=W(X_i X_j E); proves the inserted mixed derivative and both entrywise Ward identities.
* `ActualMixedWardMatrix`: defines the actual matrix B=I+u² K A over formal series and proves

  (B G)_i = u (sum_k K_ik h_k) Z,
  (B H)_ij = K_ij Z + u (sum_k K_ik h_k) G_j.

All scalar coefficients in these formulas are embedded as constant formal series. The second system includes the essential K_ij Z term; no false factorization of H is assumed. The theorem is about the actual moments, not arbitrary objects assumed to satisfy Ward equations. Empty index sets and zero coefficients are handled by the finite sum definitions.

## Grading and boundaries

The formal variable u gives degree 1 to the linear source and degree 2 to the quadratic source. Each coefficient is finite; no evaluation of a formal variable at 1 occurs. The polynomial-direction derivative is proved. The formal u-derivative identity, B's genuine unit/inverse, determinant solution, even-series descent to z=u² for the original raw block, analytic convergence/recovery, and Condition R are NOT established by this batch.

All seven modules focused-compile with only propext, Classical.choice, Quot.sound. Frozen batch-187 source and aggregation were not changed.
