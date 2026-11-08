# TournamentComponents: actual SCC relation and condensation order

The module defines Edge from actual +1 entries of a real tournament, Reach as Relation.ReflTransGen of those edges, and MutualReach as two-way reachability. The component equivalence relation is proved; Component is its actual quotient, not a supplied partition.

Verified core:
- finite-path reachability is total in a tournament;
- MutualReach is an equivalence relation;
- representative-independent reachability;
- all edges between two distinct components have the same direction;
- the actual component quotient has a constructed finite linear order;
- strict component order is equivalent to the positive cross-edge direction together with distinct components;
- intermediate vertices on a path joining two vertices of one SCC stay in that SCC.

Lean 4.35 compilation passed. See verification/tournament_components.log. Printed endpoints have only propext, Classical.choice and Quot.sound; no sorryAx or new axioms.

Boundary: the finite enumeration of all components and an entire matrix-to-ordinal-join reindexing are not constructed here. Actual induced strong blocks and their size bounds are supplied separately by TournamentComponentBlocks.
