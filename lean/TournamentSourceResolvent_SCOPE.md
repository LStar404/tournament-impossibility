# TournamentSourceResolvent: verified actual source resolvent

## Exact statement and domain

For every actual real tournament sign matrix B, q≥0, and q*(n−1)^2<1, resolvent_eq_series proves

    (B1)^T (I+q B²)^(-1) (B1) = Σ_(r≥0) q^r ||B^(r+1)1||².

The subtraction n−1 is truncated Nat subtraction in dimension zero. The natural parameter corollary q=1/n² explicitly requires n>0 and is proved in source_resolvent_natural.

source_resolvent_le compares this genuine resolvent quadratic to the actual transitive tournament reference, not merely to an abstract formal series.

## No hidden analytic hypotheses

The caller supplies only the actual tournament and the stated scalar domain. Normality follows from skew symmetry. Full-matrix geometric summability follows from the proved zero-diagonal row bound. inverse_left_right proves BOTH inverse multiplication identities, so the totalized Matrix inverse is not being used at an unverified singular point. ResolventSeriesIdentity then proves the quadratic-series interchange and coefficient identity. No separate summability, invertibility, normality or resolvent-identity hypothesis is imposed on the final theorem.

## Verification

Actual serial Lean 4.35.0 compilation passed. Main log: verification/tournament_source_resolvent.log. The separate verification/SourceResolventEndpoint.lean takes raw matrix entries and only skew/±1 and scalar-domain assumptions, expanding both resolvent quadratics. See verification/source_resolvent_endpoint.log. All printed final dependencies are only propext, Classical.choice and Quot.sound, with no sorryAx or added axioms.

## Remaining limits

Only a real nonnegative parameter on the explicit sufficient row domain is asserted. This is not the optimal spectral radius, a fixed larger complex spectral neighborhood, a differentiated comparison, the six-order small-defect identity, or full Assumption R. No new six-order deficit result is claimed in this module.
