# General symmetric occurrence reindexing and full polynomial definition

Finite occurrence-pairing modules; complete verification evidence is recorded in verification/result.json.

SymmetricPairingTransport represents each actual involution's unordered
edges as a Finset of Sym2 pairs. Covariance is lifted using its PROVED
symmetry, so reversing a representative does not change its edge factor.
Theorem moment_transport gives arbitrary finite-type reindexing by an actual
conjugation equivalence of partner involutions. There is no bipartite,
zero-diagonal, equal-colour-size, or rank-preservation assumption.

PairingRepresentativeBridge proves that this unordered-edge product equals
the existing unique-minimum-representative product for every injective rank.
It proves injectivity of the representatives-to-edges map and equality of
its image with ALL actual edges. occurrence_moment_eq connects the new
unordered sum to the older RepeatedLabelPairing.moment. arbitrary_reordering
therefore proves arbitrary permutations of its 2n positions, including
mixing the two formerly distinguished colours, for general symmetric C.
This is not the old zero-monochromatic/per-colour theorem under a new name.

OccurrenceWickPolynomial defines Occ(d)=Sigma i:L, Fin(d i), for a finite
coordinate type L. Its monomialMoment sums actual occurrence pairings;
zeros of d create no occurrences, and multiplicities create distinct ones.
The wick map is a genuine S-linear coefficient extension on ALL multivariate
polynomials, with proved monomial action c*monomialMoment(d). An arbitrary
bijection enumerating Occ(d) computes the same moment by the checked general
transport theorem. No value is replaced by a target exponential formula.

All three modules focused-compiled and generated oleans. Reported endpoints
have only propext, Classical.choice, Quot.sound; no sorryAx.

Remaining: a separate explicit Occ(squarefree exponent) equivalence and proof
that the FULL polynomial wick agrees with the earlier squarefree contraction
on the squarefree subspace; general deletion recursion and moment counts;
linear/quadratic exponential formal identities; Gaussian probability or
analytic integral interpretation; analytic tails/recovery bounds. These are
not implied just by defining the full linear map. In particular full
Condition R and exponent re-summation remain unproved.
