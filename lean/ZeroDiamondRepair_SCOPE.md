# ZeroDiamondRepair: end-to-end zero-diamond repair endpoints

## What the final theorems actually take

An actual finite `DiamondGap.Tournament V`, the existing unordered diamond
count hypothesis `T.diamonds.card = 0`, and its order `|V|=2k+1` or `|V|=2k`.
No color representation, normalization, repair metric, energy formula,
transitivity, or target-identification premise remains in these endpoints.
The empty even case and the one-vertex odd case are included.

`tournamentEnergy T` is defined directly from the ORIGINAL tournament:

    E(T) = Σ_{a∈V} (Σ_{b∈V} T.S(a,b))².

The integer entries are cast to reals only for the numerical bound.
`finiteMismatch` counts actual distinct undirected differing edges, once
per edge using i<j. It is not an abstract potential or an assumed distance.

## Final endpoints

### zero_diamond_odd_repair

For |V|=2k+1 and zero diamonds, produces a single ordinary enumeration
`e : Fin (2k+1) ≃ V` such that the original matrix `T.S(e i,e j)` and the
independently defined standard cyclic forward-k-neighbor carousel differ
on at most E(T)/8 undirected edges.

### zero_diamond_even_repair

For |V|=2k and zero diamonds, produces an actual base word of length k and
a single ordinary enumeration `e : Fin (2k) ≃ V` such that the original
matrix and the independent two-layer doubling

    D(B) = I⊗J₀ + B⊗ttᵀ,  J₀=[[0,-1],[1,0]], t=(1,-1),

differ on at most (E(T)-|V|)/16 undirected edges. Here B is the actual
k-vertex colorGraph of the returned base word, known to be a tournament
by `colorGraph_tournament`. `flatDoubling` merely uses the explicit ordinary
interleaved labeling of this independent two-layer construction; it does not
define a doubling to mean an arbitrary paired word.

## Verified composition

The proof calls the actual zero-diamond color representation theorem,
retains its original-vertex enumeration, applies the verified arbitrary-word
cut/repair results, transfers energy back to the original finite tournament,
uses the independently proved named-target isomorphisms, and composes all
ordinary permutations into the final e.

The auxiliary module `FiniteGraphEditTransport` proves:
* equality of the natural-label and finite-label differing-edge counts;
* invariance of the true undirected count under simultaneous ordinary finite
  relabeling of both skew matrices.

The latter theorem is needed because sorting edges by i<j must not silently
assume that a permutation preserves the vertex order. Its proof separately
counts both orientations and proves the two half-counts agree.

No sign switching is substituted for an ordinary graph isomorphism. The
sign-switch argument used inside the representation theorem reconstructs the
original matrix; all final reindexing is by explicit ordinary equivalences.

## Remaining scope

This module supplies complete finite zero-diamond repair theorems. It does
NOT supply repair for positive diamond count, quantitative analytic feedback,
near-extremal stability, Hamiltonian count variation, or the full condition R.
The constants here must not be used outside the stated zero-diamond hypothesis
without a separately verified extension.

## Audit

New sources: `lean/ZeroDiamondRepair.lean` and
`lean/FiniteGraphEditTransport.lean` (each with its own scope).
Final commands compiled both source modules successfully, exit code 0 and
no warnings. Five endpoint/helper axiom audits in ZeroDiamondRepair and four
in FiniteGraphEditTransport list only standard propext, Classical.choice,
Quot.sound. No sorry/admit, new mathematical axiom, unsafe proof or external
oracle was introduced.

Logs:
* `verification/ZeroDiamondRepair.log`
* `verification/FiniteGraphEditTransport.log`

Included in full `verify.py`, `lakefile.toml`, and independent `EndpointCheck.lean`.
