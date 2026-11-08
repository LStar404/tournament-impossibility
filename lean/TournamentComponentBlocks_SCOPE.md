# TournamentComponentBlocks: actual induced strong SCCs and size bound

`Fiber B C` is the actual vertex fiber of a mutual-reachability quotient component C. Its finite enumeration induces an actual `Tournament (size B C)` by pulling back B's entries; no strong-block decomposition is supplied as a hypothesis.

Verified endpoints:
- `path_in_fiber`: every actual directed path between vertices in a component lifts into that induced vertex fiber. The proof uses return reachability to certify every intermediate vertex belongs to the same component.
- `induced_strong`: the actual enumerated induced component is strongly connected.
- `induced_cycleCount_le`: an explicit injection of ordered cyclic triples proves its cycle count is at most the global count.
- `component_size_le_cycleCount`: if the global ordered cycle count is positive, every actual SCC size is at most that count. Nontrivial SCCs use the proved vertex-triangle theorem; singleton SCCs use positivity, so no size≥2 hypothesis is hidden.

Lean 4.35 compilation and the independent `actual_scc_size_endpoint` both passed. Logs are verification/tournament_component_blocks.log and verification/tournament_component_endpoint.log. All printed dependencies are propext, Classical.choice, Quot.sound; no sorryAx/new axioms.

This gives a real graph-theoretic component-size bound. The finite enumeration of all components into one ordinal block join and the full-matrix reindexing are separate remaining constructions.
