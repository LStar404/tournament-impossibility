# Actual strong-block triangle coverage

Strong means actual directed reachability between every ordered pair, using
Relation.ReflTransGen on the matrix's +1 edges. Nontrivial strong tournaments
are proved to contain a directed three-cycle through every vertex. An explicit
injection from vertices to actual ordered cyclic triples proves n≤cycleCount.
No target count bound or cycle existence is assumed.

The family bound uses genuinely strong constituent blocks but does NOT assert
that an arbitrary input graph has already been decomposed into these blocks.
The numerical h≤12D/n interface retains the pivot-link averaging inequality as
an explicit input until connected to that separately verified graph theorem.
