# TournamentEnergySeries scope

Actual Lean 4.35 compilation passed.
- energy_le proves actual all-one/source power energy ||B^r1||² ≤ ||T^r1||² for all n,r in Nat and every actual tournament B.
- weighted_energy_le proves every finite nonnegative weighted combination of these energies is dominated.
- finite_source_series_le proves all truncated sums Σ_(r<N) q^r ||B^(r+1)1||² are dominated for q≥0.
- source_series_le passes to infinite sums ONLY under explicit summability hypotheses for both series. Convergence is not assumed away in the later convergence modules, which supply sufficient numerical domains separately.

This module does not identify the series with a matrix resolvent or prove a full complex stable spectral domain or Assumption R. Log: verification/tournament_energy_series.log; standard three axioms only.
