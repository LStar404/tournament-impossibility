# TournamentEnergyRowDomain scope

Actual Lean 4.35 compilation passed.

## Explicit strengthened domain

The true zero diagonal is removed from each row sum, giving the bound based on d=(n−1) as a truncated natural number. The proof supplies the majorant

    q^r ||B^(r+1)1||² ≤ n*d²*(q*d²)^r.

For every actual tournament B, q≥0 and q*d²<1, source_summable proves convergence and source_series_le proves

    Σ_r q^r ||B^(r+1)1||² ≤ Σ_r q^r ||T_n^(r+1)1||².

No summability hypothesis is imposed on the caller. The natural parameter q=1/n² belongs to this domain for every n>0, and source_series_at_inverse_square provides that endpoint directly. The empty dimension is supported by the general domain theorem, but the inverse-square corollary explicitly requires positive dimension.

## Limits

This is a real nonnegative-parameter source-energy series comparison. It does not assert a matrix-resolvent identity, the optimal spectral convergence radius, a fixed larger complex stable neighborhood, differentiated inequalities, the small-defect sixth-order identity, or full Assumption R. Natural exponents only.

Log: verification/tournament_energy_row_domain.log. Standard propext, Classical.choice and Quot.sound only; no sorryAx/new axioms. The separate verification/OnesEnergyEndpoint.lean checks raw Matrix-entry inputs and expands the all-one energies.

## Subsequent actual resolvent identification

TournamentSourceResolvent now proves the actual source-resolvent identity and comparison, including both inverse multiplication identities, on the same sufficient real domain q≥0, q*(n−1)²<1 (truncated Nat subtraction), including q=1/n² for n>0. This supersedes earlier exclusions of resolvent identification; no optimal/expanded complex domain, differentiated comparison, sixth-order small-defect identity or full R is proved.
