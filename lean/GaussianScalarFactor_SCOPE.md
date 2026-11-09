# Uniform scalar Gaussian-factor error

The defined factor is G=prefactor/H_n(i*k), with the beta-log branch and
substitution k from GaussianParameterBranch. Finite bounds and an eventual
radius-only threshold prove |G-sec(z)|<=C(r,R)/n uniformly for |z|<=r,
0<=r<R<pi/2. The constant is explicit in errorConstant. G(0)=1 is proved.
The estimate uses actual log-branch error, finite-kernel error and zero-free
disk bounds; it does not assume the Gaussian error as an input.

The exact inverse-square-root graph determinant relation is proved separately
in GaussianDeterminantBranch. Neither module alone establishes a raw Gaussian
integral formula, block-source elimination, or permanent recovery.
Focused compilation passed, standard logical axioms only.
