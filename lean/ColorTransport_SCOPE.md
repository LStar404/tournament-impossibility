# ColorTransport: machine-checked finite swap reachability

This is an independent extension after ColorEnergy, not a proof of R.

## Concrete objects, not assumed transport axioms

Words are actual `List Bool` values: true means +1, false means -1.
`charge` is the integer difference between the two color counts;
`charge_eq_sum` proves it equals the sum of the ±1 values.

`Swaps n u v` is an inductively generated derivation using exactly n
adjacent unlike-color swaps. Its only elementary move exchanges the first
two different colors, a `cons` constructor moves a derivation beneath a
fixed prefix without charging a step, and transitivity adds step counts.
Thus there is no arbitrary edge/word transition admitted as a hypothesis.

## Proved

* `Swaps.perm`: every such swap derivation is an actual list permutation.
* `perm_has_swaps`: every permutation has a finite swap derivation;
  trivial equal-letter swaps are eliminated rather than charged.
* `perm_of_length_charge`: for binary words, equal length and charge imply
  permutation equivalence. This follows from the two actual color counts.
* `equal_total_reachable`: any two actual words of equal length and total
  color can be transformed by finitely many adjacent unlike-color swaps.
* `paired orient`: explicit list of pairs `[a, !a]`, with arbitrary chosen
  orientation of every pair; proved length `2 * orient.length`, charge zero.
* `paired_even_prefix` and `paired_odd_prefix`: even prefix charge is zero;
  odd prefix charge is exactly the selected pair color, with an explicit
  in-range hypothesis for the latter.
* `reaches_paired`: every balanced word reaches every explicitly chosen
  paired target of the same length.
* `alternatingOdd k`: concrete `+ - + - ... +` target of length `2k+1`
  and charge 1; `reaches_alternatingOdd` proves reachability from every word
  with those length and total-color values.
* `area`: concrete recursively summed absolute suffix +1-count discrepancy.
  `area_triangle` proves its triangle inequality for equal-length words.
* `area_le_swaps`: every n-step swap derivation has `area u v ≤ n`.
* `minimum_swaps_exists`: there is a least attainable swap count, with
  an actual derivation, minimality over all derivations, and the area
  lower bound. The proof uses well-ordering of natural numbers, not an
  assumed minimum or transport-distance axiom.

## Not proved within this module

* Attaining the area lower bound; in particular, this file does NOT prove
  `minimum swaps = area = (1/2) Σ |P_i-P'_i|`.
* The formal equivalence of this suffix-count area with the usual prefix
  color-discrepancy sum (the mathematical equivalence uses equal totals).
* Selecting the energy-optimal target from signs of the input's odd prefixes
  and combining its budget with exact attained distance.
* The matrix/tournament correspondence, one graph edge reversal per swap,
  full e/16 and E/8 graph-edit bounds, or the general condition R.

The new existence theorem removes the earlier gap of whether such targets
are actual reachable finite words. It does not remove the quantitative
optimal-transport gap, so the ColorEnergy scope must not be overclaimed.

## Verification

2026-11-08: `lake env lean ColorTransport.lean` completed with exit code 0,
no compiler warnings. The seven printed exported theorem axiom sets contain
only standard `propext`, `Classical.choice`, `Quot.sound` (some are smaller).
No `sorry`, `admit`, new `axiom`, or unsafe declaration is introduced.
Integrated into `lakefile.toml`, `verify.py`, and `EndpointCheck.lean`.
Compiler/axiom log: `verification/ColorTransport.log`.

## Subsequent formalized extension

`ColorTransportExact.lean` now supplies actual input-prefix parity, explicit
energy-optimal paired/alternating targets, minimum-distance attainment and its
prefix-sum identity, and real color-word swap paths bounded by E/8 and e/16.
The corresponding gaps listed above concern this module alone and are closed
by that extension. Matrix row-score identification, graph-edge correspondence,
full graph-edit bounds outside the word model, and R remain unproved here.
See `ColorTransportExact_SCOPE.md` for exact statements and limits.

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
