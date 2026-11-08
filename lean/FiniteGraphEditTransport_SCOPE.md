# FiniteGraphEditTransport: ordinary finite reindexing of actual edge counts

This module imports ColorGraphRepair and supplies counting/reindexing helpers.
It does not introduce a new abstract distance or assume any switching invariance.

## Objects

`finiteMismatch N B C` is the actual finite set of pairs `(i,j) : Fin N × Fin N`
with `i < j` and `B i j ≠ C i j`. Each distinct undirected differing edge is
counted exactly once. It is defined by filtering the finite universal pair set.

`restrictNatEquiv N e he` restricts an actual equivalence of natural labels to
`Fin N`, using the explicit premise `∀ i, e i < N ↔ i < N`. Its inverse and
both inverse identities are provided and proved. The empty vertex set is allowed.

## Verified public theorems

* `finiteMismatch_reindex_card`: for two real skew-symmetric matrices on
  `Fin N`, simultaneously applying the same ordinary vertex equivalence to
  both matrices leaves `finiteMismatch.card` unchanged.
* `finiteMismatch_nat_restriction`: the finite edge count for
  `B i j` versus `C (e i) (e j)` equals the existing
  `mismatchEdges N B C e` count on natural labels. This counting equality
  itself needs no finite-preservation premise on e; such a premise is separate
  when interpreting e as a permutation of the finite vertex set.
* `finiteMismatch_nat_identity`: the identity-label specialization.

## Proof method

For skew matrices, a differing diagonal entry is impossible. The complete
ordered differing-pair set splits into disjoint `i<j` and `j<i` halves.
Swapping the two endpoints gives a bijection of the halves because both
matrices are skew. Thus the ordered count is twice the undirected count.
The product ordinary equivalence `e × e` preserves the ordered count, yielding
the desired undirected cardinality invariance. The natural/finite bridge uses
an explicit bijection given by taking the two `Fin` values.

No switch of vertex signs appears in the reindexing theorem. The skew premises
are necessary for the stated undirected-count proof and are exposed explicitly.
No graph representation, zero-diamond argument, analytic estimate or R claim
is introduced here.

## Verification

Source: `lean/FiniteGraphEditTransport.lean`.
Log: `verification/FiniteGraphEditTransport.log`.
The four exported core objects/theorems are audited using `#print axioms`.
Only standard propext, Classical.choice and Quot.sound occur (some use fewer).
No sorry/admit, new mathematical axiom, unsafe proof or external oracle.
Included in full `verify.py`, `lakefile.toml`, and independent `EndpointCheck.lean`.
Final `lake env lean -o FiniteGraphEditTransport.olean FiniteGraphEditTransport.lean`
completed on 2026-11-08 with exit code 0 and no warnings. The verified compiled
object is also available in `.lake/build/lib/lean/` for dependent modules.
