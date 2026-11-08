# MajorizationCone scope

The operator is explicitly defined by the selected-tail function P, not by an abstract cone-preservation assumption.

Verified results:
- penalty j = 1+2 floor(j/2), monotonicity and upper bound.
- P_tail_formula identifies the coefficient definition of P exactly with k sum x − sum(j<k) penalty(j) x(n−k+j).
- Nonnegative decreasing P coefficients, hence P_preserves_prefix_order.
- entry_identity and difference_prefix prove the prefix-generator image of P(k+1)−P(k).
- K_eq_coneOperator proves equality of the P-difference operator and its cone-generator expansion, using finite Abel and x(n)=0.
- K_preserves_cone: decreasing nonnegative finite input, padded by zero, gives decreasing nonnegative output.
- prefix_K: output prefix equals P, including the zero prefix.
- K_preserves_prefix_order: K preserves finite weak majorization.

No tournament selected-row bound is assumed or established in this module. It does not prove sorted |Bx| ≺ Kx, the signed-conjugacy orbit, moment comparisons, or Assumption R. The alternative anti-diagonal ±1 entry formula is not separately identified; K is defined directly as the differences of the exact P formula.

Lean 4.35.0 and pinned Mathlib. All printed axioms are standard propext, Classical.choice, Quot.sound. No sorry/admit/new axioms.

Integrated into `lakefile.toml`, full `verify.py`, and `EndpointCheck.lean`;
compiler/axiom output is retained in `verification/MajorizationCone.log`.
