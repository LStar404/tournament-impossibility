# Actual tournament ordered-block sixth deficit

`actual_deficit_formula` proves the exact reference-minus-actual sixth deficit
for every finite family of actual tournament sign matrices. Its reference is
the actual ordered join of same-sized transitive blocks. The source-energy
identity is NOT a hypothesis: it is supplied by the verified actual directed
3-cycle counting theorem and the actual transitive first-energy closed form.

`t_i` is explicitly (the cardinality of the oriented cycle triples)/3. The raw
count counts each cyclic three-set three times by cyclic rotation; no theorem
identifying this expression with a separately defined unordered-set Nat count
is claimed here.

The module also proves Q_i,L_i≥0 from already verified actual matrix/source
moment comparison, and r≤nh²/24 from actual source-energy nonnegativity.

`conditional_small_deficit` proves 6n²D≤actual sixth deficit assuming only the
listed size data n=∑m_i, n≥4, 0≤h≤n/2, m_i≤h, and D≤(n−3)r. The last inequality
is still an explicit hypothesis about the supplied real parameter D: THIS DOES
NOT YET ASSERT IT FOR A GRAPH'S DIAMOND COUNT. Nor does it derive the block size
bound from D≤n²/24 or formalize the necessary strong-block/source-switching
counting estimates. No unconditional small-diamond spectral bound or R follows
from this module alone.

The reference block join is subsequently normalized to a single T_n in the
separate OrdinalTransitiveReference layer if that layer is verified.

## Subsequent graph-count and SCC bounds

DiamondTriangleIncidence and TriangleCountBridge now supply actual unordered diamond/triangle counting identities and D≤(n−3)t. SmallDiamondComponentReduction supplies a source switch with actual maximum reachability-SCC size h≤12D/n and 2h≤n under n≥4, 0<D and 24D≤n², and PivotMomentInvariant proves actual sixth-moment invariance. The ordered full-matrix SCC join reconstruction and assembly of the unconditional final sixth-deficit bound remain unproved; R is not claimed.
