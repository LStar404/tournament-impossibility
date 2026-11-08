# ColorGraphRepair: matrix bridge and ordinary graph-edit bounds

Independent module after ColorTransportExact. This closes the local
color-word-to-matrix and edge-flip bridges; it does not establish R.

## Exact domain and conventions

A word `w : List Bool` has m = w.length vertices, labeled 0,...,m-1.
True represents +1 and false represents -1. The ambient matrix is a function
on natural-number labels, but every edit certificate and differing-edge count
restricts to indices below m. `colorGraph w i j` is

    colorR(w,i) * colorR(w,j) * orderSign(i,j),

where orderSign is +1 if i<j, -1 if j<i, and zero on the diagonal.
This is the color-word D T_m D tournament-matrix convention. Zero diagonal,
skew symmetry and squared off-diagonal entries equal to 1 are proved.
No arbitrary tournament is assumed representable by such a word.

## Completed bridges

* `colorGraph_row_sum` proves the actual finite matrix row sum equals
  c_i (A - 2P_i - c_i), using the input word's actual prefix sums.
* `graphEnergy_eq_wordEnergy` identifies the squared row-sum energy
  `Σ_i (Σ_j B_ij)^2` with the earlier ColorEnergy expression. The bridge is
  exact and does not use an external formula as a hypothesis.
* `swapEquiv k` is an ordinary permutation interchanging adjacent labels.
* `adjacent_matrix_flip` proves that exchanging adjacent colors and applying
  this permutation changes only their mutual edge (both skew entries).
  `adjacent_matrix_flip_changes` additionally proves this edge truly differs,
  since its old value has square 1. All other entries are unchanged.
* The matrix flip identity actually holds whether the colors differ or not;
  the paths imported from Swaps use only unlike-color exchanges. No vertex
  sign-switching operation is used or charged as ordinary isomorphism.

## Graph paths and final-label certificates

`GraphEdits` is generated only by ordinary relabeling followed by one-edge
reversal. `swaps_graph_edits` converts an actual counted word path to such a
counted graph path, under any fixed initial word prefix.

The result is not left solely as a path-based distance convention:
`graph_edits_certificate` composes all intermediate permutations into one
final ordinary permutation and supplies a list of n valid undirected edges
covering every final matrix discrepancy. Duplicates are permitted in that
list but do not inflate the number of distinct differing edges.

`mismatchEdges` is the actual finite set of pairs (i,j) with 0≤i<j<m whose
entries differ after the one final permutation. `mismatch_card_le` proves
its cardinality is at most the certificate list length.

## Final machine-checked graph-edit bounds

* `odd_edit_card_bound`: if m=2k+1 and total color is 1, there is an ordinary
  permutation preserving the m-vertex set such that the number of distinct
  differing edges from the explicitly constructed alternating target is
  at most E/8, where E is the actual matrix squared row-sum energy.
* `even_edit_card_bound`: if m=2k and total color is 0, there is such a
  permutation with at most (E-m)/16 distinct differing edges from the
  explicitly constructed sign-selected paired target.

Both statements include a final finite edge-discrepancy cardinality, not
merely an abstract metric bound, potential-function bound or assumed path.

## Remaining boundaries

Not proved in this module:
* normalization of an arbitrary color word by an ordinary cyclic cut;
* identification of the alternating target with a separately defined carousel
  object, or the paired target with a separately defined doubling construction;
* representing general tournaments or controlling nonzero-diamond repair;
* upstream structural stability, height estimates, Hamiltonian count changes,
  or the full condition R.

The earlier scope warnings specifically about the matrix energy formula,
one-edge bridge, or converting these color budgets to ordinary finite graph
edit upper bounds are superseded by the results in this module. Other
warnings remain applicable.

## Verification

Source: `lean/ColorGraphRepair.lean`.
Command: `lake env lean ColorGraphRepair.lean`.
Log: `verification/ColorGraphRepair.log`.
Sixteen exported core theorems are explicitly audited using `#print axioms`.
No sorry/admit, new mathematical axiom, unsafe proof or external oracle is
introduced. Only standard propext, Classical.choice and Quot.sound occur.
Integrated into `lakefile.toml`, full `verify.py`, and `EndpointCheck.lean`.
Earlier scope documents identify the matrix/edge bridges now closed.
Final compilation on 2026-11-08 completed with exit code 0 and no warnings;
all sixteen printed axiom lists contain only the standard logical axioms above.
