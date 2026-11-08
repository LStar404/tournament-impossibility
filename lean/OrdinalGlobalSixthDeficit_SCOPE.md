# Global-reference sixth deficit

This thin assembly uses `OrdinalTransitiveReference.sixth_eq` to normalize the
actual ordered join of reference transitive blocks to the single actual matrix
T_(sum block sizes). All underlying comparisons are finite actual matrices.

`actual_formula` is the precise sixth-deficit polynomial with actual cycle
counts normalized by three. `conditional_small` yields 6n²D from explicit block
size and D-versus-triangle assumptions. It does NOT prove the conditions for a
graph's diamond count, does not derive h≤n/2 from small D, and does not prove R.

The scalar D remains an arbitrary real parameter constrained by the theorem's
stated hypothesis. Do not describe this endpoint as an unconditional
small-diamond theorem or as a completed determinant/spectral gap estimate.

## Subsequent graph-count and SCC bounds

DiamondTriangleIncidence and TriangleCountBridge now supply actual unordered diamond/triangle counting identities and D≤(n−3)t. SmallDiamondComponentReduction supplies a source switch with actual maximum reachability-SCC size h≤12D/n and 2h≤n under n≥4, 0<D and 24D≤n², and PivotMomentInvariant proves actual sixth-moment invariance. The ordered full-matrix SCC join reconstruction and assembly of the unconditional final sixth-deficit bound remain unproved; R is not claimed.

## Actual-graph endpoint

`ActualSmallDiamondSixth.actual_small` discharges the decomposition, component-size,
and triangle-count inputs for actual tournaments satisfying `n >= 4`, `D > 0`,
and `24*D <= n^2`. The resulting bound is `6*n^2*D` for the difference of
transitive and input cube Frobenius square norms. The analytic R statement is
not a consequence of this finite lemma alone.
