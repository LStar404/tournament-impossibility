# TriangleCountBridge scope

Actual definitions:
- `directedTriples T`: the Finset of ordered triples with all three cyclic edge signs +1, for any finite carrier V;
- `vertices q`: the unordered vertex triple;
- `fibre T s`: those actual directed triples whose vertex set is s;
- `toReal T`: entrywise integer-to-real casting, preserving the same tournament, for V=Fin n.

Kernel proofs identify each fibre over a cyclic triple as precisely the three rotations of a positive cyclic enumeration. Distinct vertex sets have disjoint fibres. Finite union cardinality proves
  card(directedTriples T)=3*card(cyclicTriangles T).
The proof covers arbitrary finite carriers, including nested Sum types; no graph reindexing or real-number division is used to define the counts.

The real SourceEnergy cycleCount is then proved equal to this integer directed-triple count and hence to three times the unordered count.

Convenience endpoints:
- `three_diamonds_le_ordered`: 3*card(T.diamonds) <= (|V|-3)*card(directedTriples T), combining the actual incidence theorem;
- `source_energy_unordered`: actual matrix source energy = n(n²−1)/3 − 8*card(cyclicTriangles T).

These are finite exact graph counts and energy identities, not an asymptotic reconstruction theorem or Assumption R.

Verification: main module and independent expanded endpoint both exit 0 on Lean 4.35.0. Logs: verification/triangle_count_bridge.log and verification/triangle_incidence_endpoint.log. Independent endpoint: verification/TriangleIncidenceEndpoint.lean. All audited axioms are only propext, Classical.choice, Quot.sound. No sorry/admit/new axiom.
