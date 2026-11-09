# Full repeated-index polynomial Wick integration by parts

Four modules derive a reusable finite identity from the existing true involution-pairing definition.

1. `AssignmentDeletionExponent` proves that deleting one actual labelled position subtracts precisely one occurrence of its label. It proves the exponent of the full Occ(d) labelling is d and proves the Option-extension exponent. No injectivity of labels is assumed.
2. `OptionPairingDeletion` gives actual equivalences for the partner of the distinguished none position and for the residual position set after deleting that pair. It applies the previously proved all-pairing deletion recurrence and transports the residual covariance without changing labels.
3. `FullWickMonomialRecurrence` derives the true monomial recursion, with multiplicity d(j) obtained from summing over Fin(d(j)). Zero occurrences contribute zero via the empty fibre. It does not assume the desired moment recursion.
4. `FullWickPolynomialIBP` extends the monomial result by actual polynomial induction to

 W_C(X_i P) = sum_j C_ij W_C(partial_j P)

for every polynomial P, finite label type, symmetric covariance C, and commutative semiring coefficients. Repeated indices are retained throughout. This is formal algebraic integration by parts; no probability measure, positivity, invertibility, or analytic convergence is asserted.

## Remaining work

The actual mixed linear-plus-quadratic exponential coefficients, their derivative identities, the formal matrix Ward system, and the arbitrary-matrix determinant/exponential solution remain to be proved. This IBP theorem is a genuine input to those proofs, not their completion. The full raw core, analytic recovery and Condition R remain outside this batch.

All four focused modules pass with only propext, Classical.choice, Quot.sound. Frozen batch-183 source and integration were not changed.
