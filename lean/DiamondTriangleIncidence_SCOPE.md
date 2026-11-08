# DiamondTriangleIncidence scope

Uses the existing DiamondGap.Tournament and its actual unordered four-vertex diamond set `T.diamonds`.

`cyclicTriangles T` is the actual finite family of unordered three-vertex sets admitting a cyclic enumeration. It permits either common cyclic edge sign, so reversing an enumeration changes a negative orientation to a positive one.

The proof proceeds via:
1. the previously verified four-vertex ordinary diamond pattern, yielding a contained cyclic triple;
2. extensions of a triple by one vertex, defined as `(univ \ t).image (fun v => insert v t)`;
3. the upper bound card(extensions t) <= |V|-3;
4. finite union cardinality, yielding `T.diamonds.card <= (|V|-3)*(cyclicTriangles T).card`.

The count is not defined by the inequality and no density assumption is introduced.

The bridge from `cyclicTriangles` to the ordered real-matrix count in TournamentSourceEnergy is proved separately in TriangleCountBridge: cycleCount(toReal T)=3*card(cyclicTriangles T). This module does not silently assume that bridge or claim Assumption R.

Main Lean 4.35.0 compilation exits 0; verification/diamond_triangle_incidence.log prints only propext, Classical.choice, Quot.sound. No sorry/admit/new axiom.
