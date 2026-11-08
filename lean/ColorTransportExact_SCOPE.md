# ColorTransportExact: attained optimal distance and genuine repair paths

This independent module imports ColorTransport and ColorEnergy. It closes
several specific gaps documented in those earlier modules; it does not prove R.

## Actual objects and energy

Words are finite `List Bool` values (true = +1, false = -1).
The `Swaps n u v` relation is the existing concrete derivation using exactly
n adjacent unlike-color exchanges. No transport axiom or assumed path oracle
is added.

`prefixR w i = charge (w.take i)` and `colorR w i = color (w.getD i false)`
are actual real-valued prefixes and colors of the input. Their increment
recurrence and squared-color identity are proved, not assumed.

`wordEnergy w = Σ_{i<length(w)} (A - 2 P_i - c_i)^2`, where
A is the actual total color of w. This is exactly the ColorEnergy expression.
Identifying it with a tournament matrix row-score energy remains a separate
matrix bridge, not asserted in this module.

## Proof strategy and completed results

1. **Unit descent:** for unequal permuted binary words u,v, construct an actual
   one-swap neighbor w of u with `area u v = area w v + 1`.
   The proof follows a first differing color and recursively exposes an unlike
   pair; the strict count discrepancy determines the sign of the absolute value.
2. **Attainment:** well-founded induction on the nonnegative integer area gives
   `exact_swaps`: a concrete derivation whose step count equals area.
3. **Optimality:** the earlier universal lower bound now gives `exact_minimum`.
4. **Prefix formula:** prove the suffix count area equals one half the sum of
   absolute prefix color discrepancies. `prefix_exact_minimum` states
   `2*n = Σ_{i=0}^{length(u)} |charge(take i u)-charge(take i v)|`, with
   a path realizing n and a lower bound against every other derivation.
   The final prefix term is zero for these equal-total words.
5. **Odd target:** construct the actual alternating target, prove its prefix
   charges are `i mod 2`, and derive parity for actual input prefixes.
   `odd_repair_path` combines the old integer budget with an attained path.
6. **Even target:** `repairOrient` chooses each pair orientation from the sign
   of the actual input odd prefix. Prove nonvanishing odd prefixes and the
   selected target's local budget. `even_repair_path` gives a real path.
7. **Original energy constants:** connect these finite budgets to ColorEnergy:
   * `odd_energy_repair`: for length `2*k+1`, total color 1, there exists a
     swap derivation to the alternating target with `n ≤ wordEnergy(w)/8`.
   * `even_energy_repair`: for length `2*k`, total color 0, there exists a
     swap derivation to the explicit paired target with
     `n ≤ (wordEnergy(w)-length(w))/16`.
   The even proof includes the exact finite parity-indicator sum; there is no
   asymptotic approximation or hidden error term.

## Remaining boundaries

This module now closes actual target construction, finite reachability,
optimal distance attainment, the prefix-distance identity, and energy-to-
actual-swap upper bounds. Earlier scope warnings about those missing pieces
are superseded by these specific new theorems.

It does NOT prove:
* the matrix row-score identification for tournament realization;
* that an adjacent color swap, after relabeling, changes exactly one graph edge;
* a graph-edit-distance theorem or its extension from the color-word class;
* height bounds, general diamond repair, Hamiltonian-count monotonicity, or R.

## Audit

File: `lean/ColorTransportExact.lean`.
Command: `lake env lean ColorTransportExact.lean`.
Log: `verification/ColorTransportExact.log`.
Core theorem axioms are audited by `#print axioms`; only standard Lean/mathlib
`propext`, `Classical.choice`, `Quot.sound` are permitted. No sorry/admit,
new mathematical axiom, unsafe proof or external decision oracle was added.
Integrated into `lakefile.toml`, `verify.py`, and `EndpointCheck.lean`; earlier
ColorEnergy and ColorTransport scope notes point to these newly closed gaps.

Final module compilation completed on 2026-11-08 with exit code 0 and no
warnings. All nine printed core theorem axiom lists contain only the three
standard logical axioms above, including both energy-repair bounds.

## Subsequent matrix and graph-edit extension

`ColorGraphRepair.lean` now proves the actual matrix row-sum and energy
identification, the ordinary adjacent-label permutation/one-edge reversal
bridge, and a final single ordinary permutation with finite differing-edge
cardinality at most E/8 or (E-m)/16 for the stated normalized color-word inputs.
Earlier matrix/edge-bridge warnings above describe this module in isolation
and are superseded by that extension. Arbitrary-input normalization,
identification with separately named carousel/doubling targets, general
nonzero-diamond repair, and R remain outside these results.
See `ColorGraphRepair_SCOPE.md` for precise assumptions and conventions.

## Subsequent cut and target-model extensions

`ColorCutNormalization.lean` extends the repair bounds to arbitrary finite
color words by a proved ordinary cut isomorphism and energy invariance.
`ColorTargetModels.lean` gives ordinary finite-label isomorphisms to independent
standard carousel and doubling definitions. Earlier cut/target warnings above
are now closed by those modules. Neither extension proves that arbitrary or
diamond-free tournaments have color-word representations; general diamond
repair and R remain separate obligations.

## Subsequent zero-diamond representation

`DiamondFreeRepresentation.lean`, with `TournamentColorEnumeration.lean`,
now proves the missing representation for an actual finite tournament whose
existing unordered diamond count is zero. It constructs a real Bool word and
ordinary finite enumeration, reconstructing the ORIGINAL matrix after an
internal sign-switch argument. Earlier diamond-free representation warnings
above are superseded by this theorem. It does not represent all tournaments,
repair positive-diamond tournaments, or establish the full condition R.
