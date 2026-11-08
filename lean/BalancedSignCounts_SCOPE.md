# BalancedSignCounts scope

For an arbitrary sequence s : Nat -> Bool, `count s b n` counts the actual indices j<n with sign b, and `prior s j` counts actual earlier indices with the same sign as j. `pairs s n` sums these counts.

Kernel-checked:
- exact doubled-pair identity 2D = p²+q²−n;
- balanced split of n minimizes p²+q²;
- exact floor baseline identity for sum_{j<n} floor(j/2);
- `baseline_le_pairs` for every prefix, including the empty prefix;
- `weighted_baseline_le` for every decreasing nonnegative weight, using the verified finite Abel lemma;
- `penalty_le` for coefficients 1+2 floor(j/2), the exact selected-row penalty.

These are actual finite sign counts, not assumed prefix inequalities. This module does not itself translate a tournament matrix selected-row sum into these counts, sort selected coordinates, establish the K matrix identity, or prove Assumption R.

All printed axioms: propext, Classical.choice, Quot.sound. Compiler log: verification/BalancedSignCounts.log. Lean 4.35.0. No added axioms, sorry, or admit.

Integrated into `lakefile.toml`, full `verify.py`, and `EndpointCheck.lean`;
compiler/axiom output is retained in `verification/BalancedSignCounts.log`.
