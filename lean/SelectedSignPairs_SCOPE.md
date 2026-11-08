# SelectedSignPairs scope

This module imports BalancedSignCounts and defines an actual Bool-to-real sign function and the finite unordered-pair cost

  sum_{j<n} sum_{i<j} |sign(s_i)b_j - sign(s_j)b_i|.

Kernel-checked results:
- `edge_formula`: exact same-sign/opposite-sign edge cost for 0 <= b <= a;
- `row_formula`: exact cost contributed by the newest coordinate, with the actual same-sign count `prior`;
- `pairCost_identity`: exact internal pair cost n*sum b - sum b - 2*sum b_j*prior(s,j);
- `pairCost_le`: optimization over arbitrary signs gives n*sum b - sum (1+2 floor(j/2))*b_j. It does not assume signs already alternate.

The final theorem takes the existing DescendingNonnegative condition plus an explicit all-pairs decreasing condition. The latter is redundant mathematically but kept as an explicit input to avoid silently depending on a sorting interface.

Not covered: enumeration of a subset of tournament rows, outside-row contribution, conversion of a full tournament matrix action to this internal pair sum, or Assumption R. These are exact finite internal pair identities, not the full tournament majorization theorem.

Lean 4.35.0. No sorry/admit/new axiom. Printed dependencies: propext, Classical.choice, Quot.sound. Log: verification/SelectedSignPairs.log.

Integrated into `lakefile.toml`, full `verify.py`, and `EndpointCheck.lean`;
compiler/axiom output is retained in `verification/SelectedSignPairs.log`.
