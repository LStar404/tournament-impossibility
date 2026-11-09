# ActualBlockGaussianSource scope

Actual focused compilation exited 0 and generated the library olean.
Log: `/workspace/shared/r_upstream_audit/actual_block_gaussian_source.log`.
All three printed endpoints use only propext, Classical.choice, Quot.sound. No warnings were emitted.

`sumSolution_eq` starts with the actual inverse of the doubled block matrix applied to the doubled all-ones vector. It derives the block equation from the proved true inverse identity, applies finite elimination with the branch's proved root identity, and identifies the sum of both solution halves. The eliminated form is not assumed.

`rawSource_eq_actualExponent` assumes n>0, v²=1, beta(n,z)!=0 and a true-unit quadratic resolvent at parameter(n,z). It proves the raw bilinear expression ones^T[(B-I)B^-1]ones/2 equals the already-defined actualExponent. The all-ones contraction uses the actual skew sign matrix and actual score S1, not a proxy vector. The ambient block dimension is 2n and the division by 2 is preserved. No zero-diamond condition is needed for this exact finite identity.

`branch_square` separately assumes zero diamonds, v²=1, beta nonzero, and finiteKernel(n,parameter*I) nonzero. It proves gaussian(n,z)^2 det(B)=1. It does not weaken or remove those premises.

These statements identify the finite block-source algebra and scalar determinant branch. They do not prove a Gaussian integral representation, permanent or coefficient recovery, truncation remainders, extremal classification, or full Condition R. Eventual discharge of all these finite hypotheses in a common domain is separate work. This module itself claims no new uniform asymptotic endpoint. No previously published modules or integration files were changed.

`factor_eq_product` directly connects the origin-normalized Gaussian branch times exp(rawSource B) to `GaussianSourceProduct.product`. It is an exact algebraic identification, not an assertion that the branch is the pointwise principal square root, and not a formal pairing or integral representation. The module was recompiled after this addition, with exit 0 and only standard axioms.
