# ColorTargetModels: independent target models and ordinary isomorphisms

This module imports ColorGraphRepair and defines the target objects independently
of the color-word graph formula. It does not assert every tournament has a color
word representation, and does not prove R.

## Doubling convention and source

The manuscript convention was checked in
`/workspace/shared/r_upstream_audit/even_entry_formal_bridge.md`, around its
explicit reference construction: t=(1,-1), J₀=[[0,-1],[1,0]], and
D(B)=I⊗J₀+B⊗ttᵀ. The same convention occurs in the upstream even-global
positive-defect exclusion note.

`doublingMatrix B i r j s` independently implements this block formula on
coarse vertex × Bool layer coordinates. It is defined for an arbitrary matrix
B, not by looking up a paired color word.

`pairLabelEquiv m` is an actual finite equivalence

    Fin m × Bool ≃ Fin (2*m),  (i,r) ↦ 2*i + bit(r).

`paired_doubling_isomorphism` proves pointwise equality of all finite matrix
entries between the color graph of `paired w` and D(colorGraph w), under this
ordinary vertex reindexing. The even/odd paired-color getter formulas are proved
from the actual list constructor. The within-pair matrix J₀ and all inter-pair
blocks are checked algebraically. No switching equivalence is used.

## Standard carousel convention

`carouselMatrix k i j` is defined independently as the standard cyclic
forward-k-neighbor tournament on 2*k+1 vertices. Its piecewise comparison form
avoids truncated natural subtraction at wraparound.

`carousel_forward_distance` proves, for distinct valid vertices, that the
matrix entry is +1 exactly when the cyclic forward distance

    (j + (2*k+1) - i) mod (2*k+1)

is at most k. Thus this is the usual carousel, not the alternating color formula
under a new name.

`carouselLabelEquiv k` is an actual ordinary permutation of Fin (2*k+1).
Its map is given by a piecewise linear expression, with an explicit inverse.
`carouselIndex_eq_mod` proves that this expression is exactly

    i ↦ 2*i mod (2*k+1).

`alternating_carousel_isomorphism` proves equality of all finite matrix entries
between the standard carousel and the color graph of `alternatingOdd k` after
this permutation. Alternating color parity is proved directly from the actual
list construction. The k=0 singleton case is included.

## Boundaries and integration

This closes the naming/independent-object gap for both targets produced by the
verified color repair theorems. Those repair modules and the cut-normalization
module are not modified here. The isomorphisms are provided as reusable finite
matrix equalities and finite vertex equivalences; this file does not duplicate
all preceding edit-cardinality bounds with these names substituted.

No statement about arbitrary tournaments, general diamond repair, analytic
stability, Hamiltonian path counts, or the full R condition is made.

## Verification

Source: `lean/ColorTargetModels.lean`.
Command: `lake env lean ColorTargetModels.lean`.
Log: `verification/ColorTargetModels.log`.
Eight exported identities/equivalences are audited with `#print axioms`.
Only standard propext, Classical.choice, Quot.sound are present (some results
use a smaller subset). No sorry/admit, new mathematical axiom or unsafe proof.
Included in full `verify.py`, `lakefile.toml`, and independent `EndpointCheck.lean`.
Final compilation on 2026-11-08 completed with exit code 0 and no warnings;
all eight printed axiom lists are limited to the standard logical axioms above.
