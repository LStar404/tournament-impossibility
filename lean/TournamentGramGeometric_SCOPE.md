# TournamentGramGeometric scope

Actual Lean 4.35 compilation passed. For an actual tournament B and q≥0, C=q*(B^T B) is defined as a genuine real matrix. Its action has the explicit sup-coordinate contraction bound q*(n−1)^2, using the actual zero diagonal. The entries of C^r are bounded by (q*(n−1)^2)^r, including r=0. Thus the FULL MATRIX geometric series is summable when q*(n−1)^2<1, not only its source-energy quadratic.

This supplies a concrete convergence input for a subsequent genuine matrix-inverse identity. It does not itself identify the inverse or assert an optimal/complex spectral domain. Log: verification/tournament_gram_geometric.log. Standard three axioms only; no sorryAx/new axioms.
