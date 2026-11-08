# Actual small-diamond sixth-moment deficit

The endpoint `ActualSmallDiamondSixth.actual_small` takes a genuine
finite tournament on `Fin n`, with `4 ≤ n`, actual diamond count `D > 0`, and
`24 D ≤ n²`. It asserts `6 n² D ≤ ||T_n³||_F² - ||S³||_F²` for its actual sign
matrix S and the transitive reference T_n.

The route uses an actual source switch preserving diamonds and sixth moment,
actual SCC rank-fiber matrix reconstruction, actual triangle additivity, and
the finite ordinal sixth-moment bound. The conclusion does not assume a block
partition, block-size estimate, or a diamond-versus-triangle inequality.

This is only a finite small-defect sixth-moment theorem. It does not cover
large positive defects, prove recovery/asymptotic coefficients, establish
Condition R, or formalize the analytic source/kernel estimates.

Direct Lean compilation passed with only `propext`, `Classical.choice`, and
`Quot.sound` in the endpoint axiom report. See
`verification/ActualSmallDiamondSixth.log`. Whole-project integration remains
a separate verification step.

## Interpretation checks

- D counts unordered four-vertex subsets, not labeled embeddings.
- Source switching preserves D and the sixth moment, not the ordinary triangle count.
- For real skew matrices the stated Frobenius deficit equals
  `trace(S^6) - trace(T_n^6)`, not the reverse trace difference.
- Equality in `24*D <= n^2` is allowed. For n=4 and D>0 the smallness premise
  is impossible; this theorem does not assert a bound for the four-vertex diamond.
