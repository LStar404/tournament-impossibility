# GaussianSourceDerivative: checked scope

This module transfers the actual assembled GaussianSourceProduct value estimate
on an intermediate complex disk to every fixed complex derivative. Set
r0 = (r + R)/2 for 0 ≤ r < R < π/2 and K ≥ 0. The explicit constant is

C_j = j! * GaussianSourceProduct.errorConstant(r0,R,K) / ((r0-r)/2)^j.

For each fixed j, eventually in n, uniformly over all tournaments T on Fin n
with zero diamonds and scoreEnergy(T) ≤ K n, all complex v with norm ≤ 1,
and all z with norm ≤ r, the norm of the j-th derivative difference between
GaussianSourceProduct.product T v and exp(v*z)/cos(z) is at most C_j/n.
The n threshold is outside all graph/v/z quantifiers. C_j is nonnegative.

The proof invokes the actual eventual value and differentiability theorems,
then ComplexCauchyErrorTransfer.derivative_difference_half_gap. Neither an
external analytic-function premise nor an external value-error premise is
assumed by the final endpoints.

Boundary: the product is the defined principal-log-branch finite expression.
This does not establish its equality to a raw Gaussian integral, a permanent
recovery formula, or full Condition R. It supplies fixed-order derivatives,
not an estimate uniform in derivative order j.

Focused verification: GaussianSourceDerivative.lean compiled with Lean
4.35.0 and generated its .olean. Both final endpoint axiom reports contain
only propext, Classical.choice, and Quot.sound; no sorryAx.
