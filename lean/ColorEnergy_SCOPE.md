# ColorEnergy: verified scope

Independent finite color-word algebra, not a proof of R.

## Definitions and indexing

`P : ℕ → ℝ` is a prefix path, `c : ℕ → ℝ` its color sequence.
All sums are over `0 ≤ i < n`. The hypotheses are `P 0 = 0`,
`P (i+1) = P i + c i`, and `(c i)^2 = 1` on that range.
Thus the colors are ±1; `P n` is the final total.

`energy n A P c = Σ (A - 2P_i - c_i)^2`.
For the mathematical row score `c_i(A - 2P_i - c_i)`, its square
is the same because `c_i²=1`. The matrix/row-sum identification itself
is not included in this file.

## Proved

* General telescoping identity:
  `energy = Σ(A-2P_i)² + 2P_n² - 2AP_n - n`.
* With `A=P_n`, `energy = Σ(A-2P_i)² - n`.
* With `P_n=1`, `energy = 4ΣP_i(P_i-1)`.
* With `P_n=0`, `energy = 4ΣP_i² - n`.
* Integer discreteness `|z| ≤ z²`.
* Even-prefix repair inequality `2|2k| ≤ (2k)²`.
* Odd-prefix repair inequality `2(|p|-1) ≤ p²-1` for nonzero integer p.
* Generic summed even repair budget: local `2d_i≤q_i` implies
  `(Σd_i)/2 ≤ (4Σq_i)/16`.
* Odd-normalized prefix budget with explicit parity alternatives:
  if `(P_i,target_i)=(2k,0)` or `(2k+1,1)` at every index, then
  `Σ|P_i-target_i| ≤ ΣP_i(P_i-1)`.

## Not proved within this module

* The matrix row-score formula or tournament realization.
* Deriving parity from ±1 increments (parity is explicit in the transport theorem).
* Prefix-word target existence, minimal adjacent-swap distance formula,
  or translation of a swap into one graph edge reversal.
* Full graph-edit bounds e/16 or E/8: the finite algebraic ingredients
  are present, but the transport attainment and graph correspondence are absent.
* Height cubic lower bound, zero-energy classification, normalization by cuts,
  general nonzero-diamond repair, Hamiltonian count monotonicity, or R.

The file is independent of OrderedCancellation. It adds no `axiom`,
`sorry`, or `admit`. Included in `lakefile.toml`, `verify.py`, and `EndpointCheck.lean`.
Compilation/audit log: `verification/ColorEnergy.log`.
Standard Lean/mathlib logical axioms (`propext`, `Classical.choice`,
`Quot.sound`) are distinguished from new mathematical axioms.

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
