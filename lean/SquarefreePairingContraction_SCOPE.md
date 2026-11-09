# Squarefree pairing contraction: actual algebraic connection

This stage supersedes the missing-connection note in the earlier frozen
pairing-polynomial scope, without changing the analytic boundary.

SquarefreePairingContraction defines an actual S-linear map from the
multivariate polynomial ring on Fin n ⊕ Fin n to S. It is a finite sum of
coefficient linear maps, weighted by the ACTUAL subset pairing sums. The
squarefree exponent of (I,J) is the sum of unit exponent vectors on its
selected left and right vertices; its injectivity is proved by evaluation.
The contraction of the corresponding monomial is proved to equal that
subset pairing sum, not defined to equal a global permanent answer.

Using the independently proved product expansion and genuine linearity,
contraction_shifted_product proves contraction M of product(1+X) equals
globalWeight M. contraction_scaled_product then identifies contraction(z•M)
of that product with evaluation at z of frozenPolynomial M. This closes the
previous gap between the two finite identities.

FrozenPairingEndpoints adds Fk M 0 = 1 and both natDegree and degree bounds
≤ n for the actual frozenPolynomial. These do not need nontriviality of S.

This is explicitly a SQUAREFREE formal contraction. It is not a Gaussian
probability expectation, not a general Wick functional on repeated-index
monomials, and not an analytic integral. No exponential re-summation,
positive covariance for complex zQ, convergence, recovery remainder, or
Condition R is claimed. A future Gaussian/formal-full-Wick identification
requires a separate proof, not a renaming of this linear map.

Verification: both modules focused-compiled and generated oleans. The two
contraction endpoints and F0/degree endpoints report only propext,
Classical.choice, Quot.sound, no sorryAx.
