# RawGaussianSourceScalar: checked scope

The exact reduced scalar
n - (n + (k/n)^2 psi)/(1 + v*(z/n))
equals GaussianSourceExponent.exponent n (v*z) k psi for n>0 and
1+v*(z/n) nonzero. The source sign is negative and its normalization is n^2.
The nonzero denominator is necessary because Lean complex division is totalized.

For the actual two sign branches v^2=1, nonzero beta=1-(z/n)^2 implies
the denominator is nonzero. Substituting the actual Gaussian branch parameter
and actual score source gives ActualGaussianSourceExponent.actualExponent.
This endpoint does not assume a raw-source identity, nor does it assert one:
reducedSource is explicitly only the scalar after independent block elimination.

Focused Lean compile produced an olean. Both reported endpoints use only
propext, Classical.choice, Quot.sound. No Gaussian integral, permanent recovery,
or full Condition R is established by this module.
