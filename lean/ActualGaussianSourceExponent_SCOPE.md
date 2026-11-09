# Actual Gaussian source exponential with substituted branch parameter

The actual exponent uses a=v*z, k=GaussianParameterBranch.parameter n z,
and psi=ActualComplexScoreSource.source T k. For fixed 0<=r<R<pi/2 and
K>=0, one order threshold controls every actual zero-diamond graph of order n
with scoreEnergy<=K*n, every |z|<=r, and every |v|<=1.

The proved exponential error is <=Cs/n, where
Cs=4*exp(r)*(r^2+R^2*K*diskConstant(R)^2).
Parameter inclusion in the larger disk follows from the proved branch error
2r^3/n^2 and the positive gap R-r. The ordinary graph source estimate is
instantiated at that actual parameter; it is not an external assumption of
the final uniform theorem. The finite helper retains its source premise only
to expose the assembly step.

Focused Lean compilation passed. Both final endpoints have only standard
logical axioms. This does not alone combine the Gaussian prefactor, prove
analyticity of the full actual source product, fixed derivative rates,
permanent recovery or complete Condition R. Aggregate integration is separate.
