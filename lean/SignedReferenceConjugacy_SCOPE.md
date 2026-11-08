# SignedReferenceConjugacy scope

Source combines explicit K/T square formulas and integer zigzag arithmetic to prove a concrete signed-permutation entry relation. Q is explicitly defined by its unique signed nonzero entry in each row, Q_orthogonal proves QQᵀ=I, and the final theorem states K²=Q(−T²)Qᵀ.

STATUS: actual Lean 4.35 serial compilation passed. See verification/SignedReferenceConjugacy.log. concrete_entry, concrete_square_conjugacy and Q_orthogonal all print only propext, Classical.choice and Quot.sound. No sorry/admit/new axioms are used.

This is a finite reference identity, not an asymptotic theorem or Assumption R.

Scope boundary: this concrete square identity is an input to nonnegative-integer power comparisons, not a statement about negative powers. The separate all-ones reference-orbit identity is not proved in this module or by Q_orthogonal alone. No claim of a complete proof of Assumption R is made.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.

## Subsequent all-ones and source-energy result

ReferenceOnesOrbit now proves the actual all-ones reference orbit. TournamentEnergyRowDomain proves convergence and source-energy series comparison for real q≥0 with q*(n−1)²<1 (truncated natural n−1), including q=1/n² for n>0 without a summability premise. These later modules supersede the corresponding earlier exclusions, but do not identify a resolvent or establish small-defect sixth-order identities or Condition R.

## Subsequent actual resolvent identification

TournamentSourceResolvent now proves the actual source-resolvent identity and comparison, including both inverse multiplication identities, on the same sufficient real domain q≥0, q*(n−1)²<1 (truncated Nat subtraction), including q=1/n² for n>0. This supersedes earlier exclusions of resolvent identification; no optimal/expanded complex domain, differentiated comparison, sixth-order small-defect identity or full R is proved.
