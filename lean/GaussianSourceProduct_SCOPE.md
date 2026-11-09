# GaussianSourceProduct formal scope

Focused check completed with exit code 0; generated `.lake/build/lib/lean/GaussianSourceProduct.olean`.
Log: `/workspace/shared/r_upstream_audit/gaussian_source_product.log`.
Both printed endpoint axioms are only `propext`, `Classical.choice`, `Quot.sound`.

Defines the actual branch-fixed Gaussian factor times the exponential of the actual tournament source exponent, with target `exp(v*z)/cos z`.
For fixed `0 ≤ r < R < π/2` and `K ≥ 0`, proves one eventual threshold uniform over all zero-diamond tournaments on `Fin n` with score energy at most `K*n`, all `|z| ≤ r`, and all `|v| ≤ 1`.
The absolute value error is at most `errorConstant r R K / n`, with explicit nonnegative constant
`(1/cos R + Cg) * Cs + exp(r) * Cg`, where `Cg` and `Cs` are the proved scalar-factor and actual-exponent constants.
Both factor errors are discharged by imported actual eventual theorems, not assumed in the final endpoint.

This module proves value error only. It does not itself prove analyticity, derivative errors, graph energy bounds without the stated premise, coefficient extraction, the full paper's condition R, integration checks, or remote publication.
One harmless linter warning notes the scalar assembly lemma's explicit nonnegative-Cs premise is unnecessary; no holes or additional axioms occur.
