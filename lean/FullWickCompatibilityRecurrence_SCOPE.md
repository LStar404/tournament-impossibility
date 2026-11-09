# Full Wick compatibility and genuine all-orders pairing recurrence

Six finite Wick modules; complete validation evidence is in verification/result.json.

Compatibility:
- OccurrenceSquarefreeEquiv constructs an actual equivalence between
  Occ(exponent I J) and the selected left/right subtype sets I⊕J, with label
  preservation. The inverse laws prove the unique occurrence number is zero.
- OrderedUnorderedSubsetPairing connects arbitrary enumeration-based subset
  weights to the symmetric unordered-edge sum. It covers both branches of
  actual subsetWeight, including unequal cardinalities, without defining
  a moment to be zero or assuming a common dimension.
- FullWickSquarefreeCompatibility proves full polynomial Wick on each
  squarefree basis monomial agrees with the old contraction, then proves
  full Wick of the ACTUAL product(1+X) equals globalWeight, and after scaling
  the block covariance by z equals evaluation of the frozen F_k polynomial.
  No equality of full Wick and squarefree projection on arbitrary polynomials
  is asserted; those maps differ on repeated-index terms.

Recurrence:
- PairingDeletion constructs restriction of an actual partner involution
  after removing o and its partner, and explicit insertion from a residual
  pairing. It proves insertion recovers the original, then proves actual
  assembly injectivity and surjectivity. deletionEquiv is the resulting
  equivalence (Sigma partner≠o, Pairing(Rest o partner)) ≃ Pairing V.
- PairingMomentRecurrence proves the unordered-edge set is the inserted
  distinguished edge plus the image of residual edges; proves disjointness;
  and proves the true product weight factorization. Summing through the
  actual dependent-sigma equivalence derives
    moment_C(V) = sum_{s≠o} C(o,s) * moment_(C restricted)(Rest(o,s)).
  Covariance is only required symmetric; no colour/diagonal restriction or
  desired recurrence hypothesis is used.
- PairingMomentParity constructs a simple graph from a genuine involution,
  proves its whole subgraph is a perfect matching, and invokes the proved
  matching parity theorem to show card V is even. Therefore odd-cardinality
  moment is zero. For an empty type it constructs the unique empty pairing
  and proves the empty moment is one, not zero.

Boundary: these are formal finite moments, polynomial compatibility and
recurrence. No analytic Gaussian probability/integral interpretation, formal
linear/quadratic exponential identity, factorial/moment counting theorem,
uniform analytic tail/recovery estimate or full Condition R is asserted.
The recurrence is available for subsequent counting rather than assumed.

Verification: all six candidates focused-compiled with exit 0, produced
oleans, and printed endpoints use only propext, Classical.choice, Quot.sound.
No sorryAx. Aggregate verification/integration remains with the parent.
