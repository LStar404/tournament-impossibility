# Actual Wick local convergence and original product identification

Four candidate modules beyond frozen 223:

1. TaylorDerivativeExponential: true iterated-derivative Taylor series commutes with formal differentiation. For analytic f with f(0)=0, Taylor(exp f)=subst(Taylor f)(formal exp), proved by actual analytic chain rule, Taylor multiplication and formal first-order ODE uniqueness. No unjustified infinite-sum interchange.
2. RawSourceTaylorBridge: for every finite complex matrix Q, the genuine inverse-quadratic source q(z)=1/2 ones^T[(I+zQ−I)(I+zQ)^−1]ones is analytic near zero, vanishes at zero, and has exactly the formal raw-source Taylor series. Actual inverse analyticity and transport are discharged by the previous batch.
3. TournamentRawWickAnalytic: combines the actual Gaussian branch with this raw source. The existing descended full-Wick coefficient series is proved to give a genuine HasFPowerSeriesAt of gaussian*exp(q), for zero-diamond tournaments and v²=1. The coefficient sequence is not defined as the Taylor answer. Explicit DecidableEq-instance transport avoids expensive concrete-index definitional comparison without changing any mathematical definition.
4. ActualProductWickGerm: proves q is exactly the older RawBlockSourceIdentity.rawSource of the original blockMatrix; proves actual resolvent invertibility on a neighborhood of zero from analytic entries and determinant(0)=1; applies the existing finite elimination identity. Therefore for n>0, D0, v²=1 the actual existing GaussianSourceProduct.product has the actual descended Wick coefficients as a locally convergent expansion.

Normalization: blockQ already contains 1/n in its off-diagonal interaction. The analytic and formal matrices are I+zQ and I+X*C(Q), respectively. The u²=z descent was previously proved and is not repeated or rescaled.

Remaining: a positive local radius is now genuine, but no uniform-in-n disk radius or whole-disk series convergence is asserted here. Finite squarefree matching-polynomial recovery and uniform remainder estimates remain separate. No positive Gaussian measure interpretation, arbitrary-|v| analytic extension, or complete Condition R claim is made.

The final hasSeries endpoints are Prop-valued proof definitions with inferred exact types (printed in the focused logs). These are kernel-checked proof terms, not assumed propositions; the defProp warnings are stylistic. Frozen 223 source and aggregation files were not changed.
