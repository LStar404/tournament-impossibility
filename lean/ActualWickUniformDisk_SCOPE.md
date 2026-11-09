# Actual Wick whole-inner-disk convergence

Three candidates beyond frozen 227:
- WickAnalyticDiskTransfer: extracts actual Taylor coefficients from a genuine HasFPowerSeriesAt using uniqueness, then proves whole-open-disk HasSum from actual holomorphy via Complex.hasSum_taylorSeries_on_ball.
- ActualWickUniformDisk: for 0≤r<R<pi/2, one eventual n threshold works for every zero-diamond tournament, every v²=1, and every |z|≤r. The actual Wick series sums to the original GaussianSourceProduct.product. No energy hypothesis is required for this convergence. The radius is not merely a local or analytically continued germ; the whole closed inner disk has a proved HasSum. Pointwise helper lemmas avoid huge kernel conversion inside the eventual quantifier proof.
- WickCoefficientCauchy: generic coefficient estimate M/s^k from a genuine series and a true sphere norm bound, plus weighted coefficient l1 summability and bound M/(1−rho/s) for 0≤rho<s. These are proved conditional transfer lemmas; a graph-uniform M/energy endpoint and a tail truncation estimate have not yet been instantiated in this batch.

Limitations: no extension of the actual raw branch identification to arbitrary |v|≤1; no finite squarefree polynomial recovery, activity estimates, true permanent tail, falling-factorial restoration, or complete Condition R. The generic Cauchy bound is not represented as an already discharged finite-recovery estimate.

Verification note: an initial unsplit actual eventual proof hit the kernel heartbeat limit; a high-budget retry produced no olean and was not counted as success. Splitting coefficient_germ and pointwise proofs resolved this. The final focused run explicitly reported LEAN_EXIT=0 and standard axioms.
