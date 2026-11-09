# Global ordered residual activities: finite exact identity

Six new modules, old 272-source snapshot untouched.

OrderedVertexWord constructs the actual repeated-label word by mapping the existing degree-assignment word through a vertex-label map. Its polynomial and affine polynomial equal the products over Sigma vertex occurrence positions. The affine Wick identity and existing physical moment theorem identify that word's physical moment with the real partial matching sum on those positions. No injectivity of numerical labels and no loop removal.

OrderedResidualPolynomial rewrites the actual residual polynomial coefficient as an ordered structural-vertex sum with scalar (1/b!)*product log coefficients. The scalar is implemented via algebraMap from the rational 1/b!, whose transport through S into MvPolynomial is proved.

OrderedResidualTilted applies the actual additive tilted functional, not a ring homomorphism, to this identity. Homogeneous length m and the genuine physical even expansion prove equality with the previously independently defined momentCoefficient.

PartialMatchingActivityGrouping regroups the real partial matching coefficient into j<=k, retaining only j+b<=k. The omitted terms are zero by the proved physical weight order, not stipulated zero.

OrderedResidualActivities.actual_coefficient gives the actual residualZ coefficient as finite sums over m<=2k, b<=floor(m/3), arbitrary vertex labels, degree assignments, and real partial matchings. Degrees below three vanish by actual logarithm coefficients. All repeated labels, same-vertex pairs, and singleton positions survive.

GlobalActivityFiniteRegroup.actual_regroup puts the finite j sum outermost in the actual residual coefficient identity. activity_constraints proves a structural term vanishes outside b<=2j, m<=6j, j+b<=k. Empty structures remain included; j is not the formal coefficient degree k.

This closes the finite formal structural regroup, not the asymptotic quantitative theorem. Still absent: uniform entry/norm bounds converted into activity estimates, count/label summation estimates yielding (D j/n)^j, controlled truncation/projection and falling-factorial restoration, the independent permanent true tail, and full R. No summation at u=1 or convergent infinite activity expansion is asserted. No positive Gaussian interpretation of the indefinite raw covariance is used.
