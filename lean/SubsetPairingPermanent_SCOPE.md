# Rectangular and subset finite pairing bridge

Four finite pairing modules; validation evidence is recorded separately in verification/result.json.

- RectangularPairing defines ALL fixed-point-free involutive partner
  permutations on Fin a ⊕ Fin b, with one factor per unordered edge.
  A bipartite partner gives an actual equivalence Fin a ≃ Fin b. Hence for
  a≠b every pairing has a same-colour edge, so the zero-diagonal-block
  covariance weight vanishes. This is proved, not assigned by definition.
- FinitePairingTransport constructs genuine conjugation equivalences for
  partner permutations on arbitrary types and proves finite sum transport
  for arbitrary finite left/right types with explicit enumerations. Keys
  order each colour by those enumerations, left before right.
- FinitePairingPermanent proves unequal-size covariance pairing sums zero
  and equal-size pairing sums equal the permanent of the explicitly
  enumerated square matrix. It transports to the previously checked full
  pairing theorem, reconciling finite-enumeration instances extensionally.
- SubsetPairingPermanent instantiates those theorems on actual different
  subtype sets I,J of Fin n. Restriction A I J is defined before taking the
  pairing sum. Equal cardinalities yield the permanent of the actual
  restriction enumerated by I.equivFinOfCardEq and J.equivFinOfCardEq;
  unequal cardinalities yield zero. Empty subsets are allowed.

The theorem weights use the stated explicit enumeration. A separate general
invariance theorem under changing enumerations is not asserted here. In the
equal-size symmetric-block case the resulting permanent is invariant under
row/column permutations by existing mathlib theorems, but an additional
packaged enumeration-independence endpoint has not been added.

Scope: finite full-pairing algebra on selected subsets only. The global
product-of-(1+X) subset expansion, grouping by k into a frozen F_k polynomial,
a Wick moment-functional identification, Gaussian integral, exponential
re-summation, analytic tails and permanent-recovery errors are not proved by
these modules. No positive measure for complex zQ, or full Condition R, is
claimed.

Verification: all four candidates focused-compiled with exit 0 and generated
oleans. Printed endpoint dependencies are only propext, Classical.choice and
Quot.sound; no sorryAx. Aggregate integration is left to the parent.
