# Explicit normalized beta-log branch and substitution

Define beta=1-(z/n)^2, logBeta=Complex.log beta, root=exp(-logBeta/2),
k=z*root and prefactor=exp(-n*logBeta/2). Under the stated finite-order
smallness conditions, beta belongs to the slit plane and is nonzero; the
root satisfies root^2*beta=1 and is normalized to1 at z=0. The parameter
error is <=2R^3/n^2 and prefactor error <=2R^2/n on |z|<=R.
Closed-disk differentiability is proved from these definitions and branch
conditions, not supplied as an assumption.

This chooses a branch normalized at the origin. It is NOT a claim that the
whole graph determinant's pointwise principal square root is being used.
The graph determinant identity and product estimates are separate modules.
Focused compilation passed, standard logical axioms only.
