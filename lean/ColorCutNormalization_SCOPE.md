# ColorCutNormalization: arbitrary color-word cuts and ordinary isomorphism

This module extends ColorGraphRepair from already normalized color words to
all finite color words. It does not assert that arbitrary tournaments admit
color-word representations, and does not prove R.

## Objects and exact normalization

`cutWord w k = w.drop k ++ (w.take k).map Bool.not`.
This moves the initial k colors to the end and negates those moved colors.
It preserves the length and changes total color A into A - 2P_k.

`charge_prefix_ivt` proves a discrete intermediate-value property for the
actual finite ±1 word by induction. No continuous IVT, monotone-prefix
assumption, or assumed normalization lemma is used.

Choosing P_k = floor(A/2) gives total A mod 2, which is proved to equal the
parity of the actual word length. This also covers negative A correctly
using integer Euclidean division; a separate global sign change is unnecessary.

## Ordinary graph equivalence, not switching equivalence

`rotateIndex a b` explicitly exchanges the two consecutive blocks and fixes
outside labels. Its inverse, ordinary Equiv, and preservation of the finite
vertex set are proved.

`cut_blocks_isomorphic` checks the actual colorGraph matrix entries. Negating
moved colors exactly cancels the changed transitive order for cross-block
pairs. Thus the whole cut operation is an ordinary vertex isomorphism.
This does NOT license arbitrary vertex sign switching as an isomorphism.

`normalized_graph_exists` produces the actual normalized word and the actual
finite-vertex-preserving permutation, with equality of all valid matrix
entries after that permutation.

## Energy and general color-word bounds

`sum_range_equiv` proves the required finite-sum reindexing.
`graphEnergy_isomorphism` proves squared row-sum matrix energy is invariant
under an ordinary isomorphism. `normalized_graph_energy_exists` combines
this with the explicit cut representative.

`mismatch_card_pullback` pulls a genuine exceptional-edge list through the
initial ordinary permutation, with no increase in its length.

Final endpoints, with no total-color normalization assumption:

* `arbitrary_odd_word_repair`: for ANY word of length 2k+1 there is an ordinary
  finite-vertex permutation giving at most E/8 distinct differing edges from
  the actual alternating target `alternatingOdd k`.
* `arbitrary_even_word_repair`: for ANY word of length 2k there is an actual
  orientation word of length k and an ordinary finite-vertex permutation
  giving at most (E-m)/16 distinct differing edges from its paired target.

Here E is the actual matrix squared row-sum energy, and differing edges are
counted by the finite set `mismatchEdges`, once each using i<j. These are not
merely abstract potential bounds or paths with assumed attainability.

## Scope still not covered

* Whether a general tournament belongs to this color-word graph class; in
  particular, this module does not prove a diamond-free representation theorem.
* Identification with independently defined carousel/doubling objects is
  provided separately by the verified ColorTargetModels module.
* General nonzero-diamond repair, upstream analytic stability, Hamiltonian
  count variation, or the complete condition R.

Earlier scope warnings specifically about arbitrary COLOR-WORD cut
normalization, ordinary cut isomorphism, or preservation of energy are now
superseded by this module. Warnings concerning arbitrary tournaments remain.

## Audit

Command: `lake env lean ColorCutNormalization.lean`.
Log: `verification/ColorCutNormalization.log`.
Final compilation completed 2026-11-08 with exit code 0, no warnings.
Eight core exported endpoint axiom audits list only the standard logical
axioms propext, Classical.choice and Quot.sound.
No sorry/admit, new mathematical axiom, unsafe proof or external oracle.
Included in full `verify.py`, `lakefile.toml`, and independent `EndpointCheck.lean`.
