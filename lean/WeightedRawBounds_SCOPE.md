# Weighted coefficient products and raw inverse entry scaling

Seven new candidate modules. Previous 278 sources/aggregation unchanged.

WeightedCoefficientNorm defines the actual weighted absolute coefficient tsum and a separate summability predicate. It proves the actual convolution inequality, summability of products, and submultiplicativity via the Cauchy product of nonnegative summable real sequences. No divergent tsum is treated as a norm bound without summability.

WeightedCoefficientProducts proves genuine finite product summability/bounds, and converts an actual HasFPowerSeriesAt plus larger-circle bound into weighted coefficient l1 on a smaller radius.

PartialMatchingWeightedBound applies this algebra to the existing singleton and Sym2-edge products. Actual edgecard gives B^e E^h. Summing over all structural label maps gives |I|^b, with repeated labels and loops retained. This is a real bound on the old weights, not a redefinition, but W/eta finiteness and entry coefficient-norm bounds remain explicit hypotheses.

EuclideanBilinearContraction proves complex bilinear (not Hermitian) row-inverse-column norm bounds by using conjugation in the inner-product comparison. RawResolventEntryBound derives the exact identity A R=A-A R A from R(1+A)=I, then bounds W=(zQ)R using true QRQ contractions.

RawResolventMeanBound proves a vector l2 bound from coordinate bounds, and the actual mean ((zQ)R)1 bound, with separate Q1 coordinate and l2 hypotheses. It never replaces those by score energy.

RawBlockInverseScaling discharges the row/column l2 estimates in dimension 2n using |Qij|<=C/n and |(Q1)i|<=K/n. For n>0 and a true inverse R(1+zQ)=I with operator norm<=L, it proves
  |Wij| <= (s C+2 s^2 C^2 L)/n,
  |eta_i| <= (s K+2 s^2 C L K)/n.
These are conditional raw matrix theorems, NOT a claim that the graph hypotheses or common disk inverse bound have been discharged.

Remaining: actual graph/block inverse disk bound and formal-coordinate analytic coefficient identification needed to apply the new weighted analytic theorem; coordinatewise score bridge (energy<=Kn alone is insufficient); exact partial-matching count/factorial estimates and complete (D j/n)^j bound; independent permanent true tail; falling-factorial restoration; full R. Current results supply real products/label sum estimates and the right dimension scaling but do not close these gates.
