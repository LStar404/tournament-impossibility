# TournamentEnergyConvergence scope

Actual Lean 4.35 compilation passed. The entry bound and an explicit finite row-sum estimate give ||B^r1||² ≤ n*(n^r)^2. This yields a geometric majorant and proves convergence of Σ_r q^r||B^(r+1)1||² when q≥0 and q*n²<1. source_series_le_small proves the source-energy series comparison on this domain without external summability hypotheses.

This conservative domain excludes the natural q=1/n² boundary; TournamentEnergyRowDomain supplies a sharper row bound and includes that point. Neither module by itself identifies a matrix resolvent or proves the optimal/complex spectral domain. Log: verification/tournament_energy_convergence.log; standard three axioms only, no sorryAx or added axioms. A nonfatal unused-variable lint warning is retained.

## Subsequent actual resolvent identification

TournamentSourceResolvent now proves the actual source-resolvent identity and comparison, including both inverse multiplication identities, on the same sufficient real domain q≥0, q*(n−1)²<1 (truncated Nat subtraction), including q=1/n² for n>0. This supersedes earlier exclusions of resolvent identification; no optimal/expanded complex domain, differentiated comparison, sixth-order small-defect identity or full R is proved.
