# Frozen partial-pairing polynomial: scope

Three finite polynomial modules; validation evidence is in verification/result.json:

* SubsetPairingScaling.subsetWeight is an actual full involution pairing
  sum on the selected two subsets. BOTH cardinality branches are genuine
  sums. The equal-size branch aligns enumerations to a common Fin type;
  the unequal-size branch uses each subset's own enumeration. Zero and
  permanent identities are theorems, not definitions. The smul theorem
  proves scaling covariance by z supplies z^|I|, one factor per edge.
* FrozenPartialPairingPolynomial defines globalWeight by summing all selected
  subset pairing sums. Fk M k sums the actual terms over both size-k subset
  families. By unequal-size vanishing and finite powerset-card grouping,
  globalWeight (z • M) = sum_{k=0}^n Fk M k * z^k. frozenPolynomial is an
  actual Polynomial, with its evaluation equal to that globalWeight.
* ShiftedProductSubsetExpansion independently proves the universal
  commutative-semiring product(1+X) double-subset expansion, including its
  specialization to MvPolynomial. This has no moment hypothesis.

M is fixed independently of z in the polynomial theorem. Substituting M(z)
subsequently does not make Fk(M(z)) constant when differentiating in z.
Scaling every vertex variable instead of covariance would supply z^(2k),
not the present per-edge z^k convention.

Important remaining boundary: the product expansion and pairing polynomial
are two proved finite identities. A squarefree pairing-contraction map has
NOT yet been supplied to connect them. No actual expectation, Gaussian
measure, Wick moment identification, infinite exponential re-summation,
analytic continuation, recovery bound, or full Condition R is asserted.
No standalone coefficient/degree/F0 endpoint has been added this round.
