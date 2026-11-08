# BasisReference scope

Identifies the actually sorted absolute first basis vector with that same basis vector. This is needed to turn the K comparison trajectory into a concrete first-column matrix-power norm, rather than leaving an unspecified sorted-basis orbit.

Actual Lean 4.35 compilation passed. Log: verification/BasisReference.log. Printed dependencies only propext, Classical.choice and Quot.sound; no sorryAx or added axioms.

Included in full `verify.py`, `lakefile.toml`, and the raw-matrix independent
`ReferenceMomentEndpoint.lean`/`EndpointCheck.lean` audits.

## Subsequent all-ones and source-energy result

ReferenceOnesOrbit now proves the actual all-ones reference orbit. TournamentEnergyRowDomain proves convergence and source-energy series comparison for real q≥0 with q*(n−1)²<1 (truncated natural n−1), including q=1/n² for n>0 without a summability premise. These later modules supersede the corresponding earlier exclusions, but do not identify a resolvent or establish small-defect sixth-order identities or Condition R.

## Subsequent actual resolvent identification

TournamentSourceResolvent now proves the actual source-resolvent identity and comparison, including both inverse multiplication identities, on the same sufficient real domain q≥0, q*(n−1)²<1 (truncated Nat subtraction), including q=1/n² for n>0. This supersedes earlier exclusions of resolvent identification; no optimal/expanded complex domain, differentiated comparison, sixth-order small-defect identity or full R is proved.
