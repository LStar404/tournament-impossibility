# PivotCycleLink scope

Uses the common DiamondTriangleIncidence.IsCyclic/cyclicTriangles definitions. Explicitly switches the chosen pivot to a source, proves diamond switching invariance, moves any pivot to the first Pfaffian witness position, and constructs the erase/insert bijection between its actual diamond link and cyclic triangles away from that source. Since a source lies in no cycle, the final bound also uses the shared all-cyclic-triples API.

Verified endpoint: exists p, n*card(cyclicTriangles(sourceSwitch T p))≤4D for nonempty finite tournaments. This is division-free and equivalent over the reals to r≤4D/n when n>0. Triangles and diamonds are unordered subsets, not ordered witnesses.

VERIFIED: direct Lean compilation to matching .olean succeeded. cycle_count_eq_link, exists_pivot_few_cycles and exists_pivot_total_cycles depend only on propext, Classical.choice and Quot.sound. Independent PivotCycleEndpoint.lean starts from a raw integer skew sign matrix and also verifies the switching signs and source property. Its endpoint has the same three standard axioms. Logs: verification/pivot_cycle_link.log and verification/pivot_cycle_endpoint.log. Harmless linter warnings remain; no full-project build is claimed.

This does not prove a feedback-arc repair theorem, SCC decomposition, or the final quantitative stability rate. Those are separate downstream steps.
