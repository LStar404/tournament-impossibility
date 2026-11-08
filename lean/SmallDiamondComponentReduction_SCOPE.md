# Actual SCC size bound after source switching

The theorem uses genuine reachability SCCs of the actual switched sign matrix.
maxComponentSize is the finite maximum of the cardinalities of those actual
component fibers, not a supplied block-size parameter.

For actual n≥4 and diamond cardinality D with 0<D and 24D≤n², it produces a
source switch whose actual maximum SCC size h satisfies nh≤12D and 2h≤n;
the real-number interface gives h≤12D/n. All earlier link/cycle and SCC size
bounds are discharged internally. It also retains source status and actual
sixth-moment invariance.

What this module does NOT claim: a complete finite ordered enumeration of the
SCCs, the full matrix isomorphism to the recursively constructed ordered block
matrix, the final unconditional sixth-deficit lower bound, or R. The finite
component order and induced strong blocks are verified separately, but the
remaining ordered-join reconstruction must be explicitly proved before
applying the ordinal sixth-deficit theorem to every input tournament.

## Subsequent bridge

The formerly outstanding ordered-join reconstruction is now proved in
`TournamentOrdinalReconstruction.lean`, and `ActualSmallDiamondSixth.actual_small`
uses it to derive the actual finite sixth-deficit bound under `n >= 4`, `D > 0`,
and `24*D <= n^2`. This does not close the analytic Condition R proof.
