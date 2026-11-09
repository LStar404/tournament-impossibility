# Actual general mixed Wick determinant formula, formally proved

## Endpoint

`ActualMixedDeterminantFormula.actual_formula` proves for a finite label type, a characteristic-zero field S with rational algebra structure, arbitrary symmetric bilinear covariance K, arbitrary symmetric bilinear interaction A, and any source vector h:

 Z(u) = D(u) * exp(q(u)),
 B(u)=I+u²KA,
 D(u)² det B(u)=1, D(0)=1,
 q(u)=(u²/2) h^T B(u)^(-1) K h.

Z is the existing ACTUAL full Wick functional applied coefficientwise to exp(u L_h) exp(−u² Q_A/2). It includes repeated indices and actual finite coefficients. D is constructed by substituting det B−1 (proved zero-constant) into the universal rational binomial series of exponent −1/2. exp(q) is universal formal exp substituted at the proved zero-constant q. No illegal nonzero-constant formal substitution, Gaussian measure, positivity, or assumed moment/ODE/determinant formula is used.

## New proof chain (13 modules)

1. `DerivationFiniteProduct`: genuine finite-product Leibniz rule.
2. `DerivationDeterminantColumns`: actual permutation determinant derivative equals sum of column-replacement determinants; signs are handled through derivation scalar compatibility.
3. `FullJacobiDerivation`: column replacement → Cramer's rule → trace(adjugate M * DM), then full unit Jacobi Ddet=det*trace(M^-1 DM). This is not merely evaluation at zero.
4. `FormalFirstOrderUniqueness`: coefficient strong induction proves uniqueness for f'=a f with specified constant coefficient.
5. `NormalizedDeterminantBranch`: true universal binomial construction and valid zero-constant substitution give D²d=1 and D0=1 for every d0=1.
6. `ActualMixedDeterminantJacobi`: actual B gets the full Jacobi identity and actual branch.
7. `ActualDeterminantBranchDerivative`: derives 2D'+D trace(B^-1 B')=0 from the true square identity and Jacobi.
8. `MatrixDerivationInverse`: genuine entrywise product and inverse derivative under a proved unit premise.
9. `MixedCovarianceSymmetry`: proves V=B^-1K symmetric from BK=KB^T. It does not falsely assume B=I+u²KA is symmetric.
10. `MixedCovarianceDerivative`: actual B'=2uKA and V'=−2uVAV.
11. `MixedSourceQuadraticDerivative`: actual quadratic q has q0=0 and q'=u h^T v−u³v^TAv, v=Vh.
12. `MixedDeterminantCandidateODE`: actual branch*exp(q) satisfies the same explicit scalar ODE as actual Z, with trace/source signs matched.
13. `ActualMixedDeterminantFormula`: candidate constant1 plus ODE uniqueness yields equality with actual Z.

The actual Ward system and actual Z initial/ODE came from earlier batch198, not new external hypotheses. Covariance K need not be invertible; B is a genuine unit because its constant matrix is I.

## Remaining boundaries

This is the general FORMAL mixed determinant identity, not yet the analytic raw-core identity on a complex disk. The even-series descent from u to z=u² and specialization/identification with the original raw block still need explicit packaging. Analytic convergence, consistent complex branches on the target disk, matching to the existing analytic determinant/source factors, recovery/remainder estimates, and full Condition R remain separate unproved bridges. Do not equate this theorem with completed R or the final paper.

All 13 focused endpoints compiled with only propext, Classical.choice, Quot.sound. No frozen batch198 source or aggregate was modified. Full integration/fresh verification belongs to the parent coordinator.
