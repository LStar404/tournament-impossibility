# Actual rank-one quadratic Wick series and its unique unit branch

Let C be any symmetric covariance over a characteristic-zero field S, with finite label type L, let L_h=sum_i h_i X_i and c=h^T C h. No positivity or Gaussian measure is assumed.

`RankOneQuadraticCoefficients` defines the actual polynomial P=(-a/2) L_h² and the formal series F with coefficients `wick C hs (P^k)/k!`. The coefficients are not defined by a desired closed form. Using the verified general linear-source moments it proves the coefficient formula and recurrence

 (k+1)F_(k+1) = -(ac/2)(2k+1)F_k, F_0=1.

`RankOneQuadraticODE` derives the formal identity

 (1+ac X)F' = -(ac/2)F.

`RankOneQuadraticUnitBranch` proves, by differentiation and constant coefficient,

 F²(1+ac X)=1.

It proves F is a unit and is the UNIQUE solution of this square identity with constant coefficient 1. Thus this is an actual rank-one quadratic inverse-square-root branch resummation, not a conditional theorem assuming the coefficient formula or ODE. The uniqueness theorem takes another proposed branch as input, but existence and the identity for the actual Wick series have already been proved independently.

`RankOneQuadraticDeterminant` now connects this to the actual matrix: defines A_ij=a h_i h_j, proves its quadratic polynomial is a L_h², and proves det(I+t C A)=1+t a(h^T C h) over any commutative ring. For the actual matrix over power series it concludes F² det(I+X C A)=1. The determinant is computed from genuine matrix multiplication via the rank-one determinant lemma, not defined to equal the scalar denominator.

## Boundaries

This does not prove a full arbitrary-matrix determinant formula. Mixed quadratic-plus-linear sources, general matrix quadratic sources, the full raw block core, analytic convergence, and Condition R remain separate tasks. All quadratic forms here are bilinear, not Hermitian.

Four focused modules compile with the standard axioms propext, Classical.choice, Quot.sound. No frozen batch-179 source was modified.
