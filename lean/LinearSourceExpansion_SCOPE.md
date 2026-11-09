# Multivariate linear source: full finite and formal-series chain

Five modules establish actual finite identities, not assumed Gaussian moments.

* `LinearSourceOccurrences`: for every assignment of a finite position set to labels, the multiplicity exponent is the cardinality of its actual assignment fibres. An explicit equivalence enumerates every occurrence by its original position, preserving labels. The existing full occurrence pairing moment transports through this equivalence.
* `LinearSourceExpansion`: the actual polynomial `(sum_i h_i X_i)^m` expands over all assignments `Fin m -> L`; application of the existing full Wick linear functional yields the actual sum of position-pairing moments times the product of source coefficients. Repeated labels are retained with their multiplicities, including the empty case.
* `PairingEndpointEquiv`: for any true fixed-point-free involution and injective rank, minimum-endpoint representatives times `Bool` are in explicit bijection with all positions. Consequently each edge is counted once and the position cardinality is twice the representative cardinality.

* `LinearSourcePairingFactor`: assignments are genuinely reindexed through the endpoint equivalence and curried into independent two-endpoint labels for each edge. Finite product/sum distributivity gives the quadratic contraction once per edge, not twice. No moment identity is assumed.
* `MultivariateLinearFormalExponential`: the full Wick functional applied to `(sum_i h_i X_i)^m` equals the already verified constant-covariance moment with covariance `sum_ij h_i C_ij h_j`. Thus the actual series with coefficients Wick(L^m)/m! equals formal exp((h^T C h)t²/2).

The finite statements require a finite label type, commutative semiring, and symmetric covariance. The formal power-series statement requires a commutative ring with a rational algebra structure. No positivity, nondegeneracy, probability measure, moment formula assumption, or external pairing factorization assumption is introduced. Empty labels and zero-degree cases are included by the finite sum/product statements.

## Still outside this result

Quadratic-source determinant resummation, analytic convergence/Gaussian interpretation, and full condition R remain unproved by this batch. The formal linear-source identity alone does not establish those assertions.

All five focused Lean checks pass with only propext, Classical.choice, Quot.sound. No frozen batch-174 module or aggregate is changed.
