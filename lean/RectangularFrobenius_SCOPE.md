# RectangularFrobenius scope

Actual Lean 4.35 compilation passed for generic finite-type Frobenius bilinearity, rank-one inner products, and the scalar expansions of diagonal/off-diagonal cube-block squared norms.

The diagonal expansion explicitly assumes its two mixed products have values -f and f; the off-diagonal expansion explicitly assumes the source-vector sums and square norms. These are transparent intermediate lemmas, not a standalone claim that arbitrary skew matrices satisfy the final sixth-moment recurrence. The real-matrix inputs are established separately in TwoBlockSixthMoment.

See verification/rectangular_frobenius.log. Standard axioms only; no sorry or added axioms.
