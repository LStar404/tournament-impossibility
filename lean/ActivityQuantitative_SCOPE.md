# Finite structural activities: exact recovery and quantitative estimate

## Objects and identities
ActualFiniteActivity.series is a finite sum (degrees 0 through 6j) of actual existing physical covariance/mean partial-matching weights, with the original logarithmic scalar, vertex-label multiplicity and factor 1/b!. StructuralActivitySeries proves the coefficient identity with the earlier byIndex expression; ActualFiniteActivity.actual_residual proves the real residualZ coefficient is the sum of these activity coefficients for j ≤ k. This is not a replacement definition of residualZ. ActivityZeroNormalization proves C_0=1.

Repeated numerical labels and loops are retained: pairing vertices are occurrence positions. PartialMatchingFiberCount counts the actual fiber exactly as choose(D,2e)*pairFactor(e), then bounds it by 2^D D^e. StructuralActivityCount transports this to the actual activity-index fiber. OrderedDegreeCompositionCount and ActualDegreeAssignmentCount inject the actual admissible ordered degrees across all lengths into Composition(D); there is no extraneous factor counting lengths, singletons or e/h again.

## Quantitative theorem
For n>0, index type of cardinality 2n, rho≥0, M≥1 and the actual physical covariance and mean having weighted coefficient l1 norms at most M/n (and finite), QuantitativeFixedActivity.bound proves, for every j≥1,

  ||C_j||_rho ≤ (C0(M)*j/n)^j,
  C0(M) = 2^15 * 6^3 * exp(1) * M^3.

It also proves the actual activity has finite weighted l1 norm. The constant is conservative. The decisive factorial estimate retains 1/b! and uses j^b/b!≤exp(j); discarding this factor would not give j^j. Dimension cancellation uses e+h=j+b exactly. All finite norm triangles, scalar factors, cardinality bounds and degree rearrangements are proved from the existing series, not supplied as assumptions.

## Actual graph specialization
BinaryGraphActivityBound.bound combines the preceding theorem with the verified real skew margin and actual bit-graph weighted estimates. For the chosen-enumeration fixed positive depth d=r+1 family, real skew coarse entries bounded by one, n≥24, any actual Fin relabeling, real |v|≤1 and every j≥1, it gives the actual raw activity bound at rho=9/8 with

  M_r = (1025/2)*(2^(r+1)+1).

There is no externally assumed score, spectral, inverse or analytic bound in this graph endpoint. It remains a chosen-enumeration family theorem: no new canonical Fin-popcount identification is claimed. The raw activity uses the existing FullWickSquarefreeCompatibility.block, with a proved equality to the analytic bipartite block.

## Remaining limits
The j-bound is a fixed-activity/truncation estimate; it does NOT imply the infinite sum in j converges at fixed n. Permanent circle envelopes and true permanent tails, finite n falling-factorial recovery, final normalized error transfer, and the complete R conclusion remain separate obligations. Generic diamond-free or energy O(n) hypotheses still cannot replace the bounded-score structural family without a new argument. Other workers' permanent spectral/circle files are not part of this batch.
