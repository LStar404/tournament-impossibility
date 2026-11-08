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

## Subsequent complete finite vector-majorization bridge

TournamentEnvelope, TournamentSwitching, TopAbsoluteSelection and
SelectedTournamentMajorization now construct the actual matrix selected-row
envelope, selected subsets/signs, sorting and signed-permutation bridges, proving
sortedPad(Bx) weakly majorized by K(sortedPad(x)) for every actual finite tournament
and real input. `VectorMajorizationEndpoint.lean` checks the expanded inequality
from raw matrix entries. Earlier exclusions about these particular bridges
above are superseded. Reference K-orbit identities, moment comparisons and R
remain separate, unproved obligations.

## Subsequent concrete reference and moment comparison

The ReferenceMomentComparison dependency chain now discharges the concrete
K-square signed conjugacy, reference column-norm identities and all natural-power
Frobenius comparisons for actual finite tournament matrices. Earlier exclusions
about those interfaces above are superseded by that verified extension.
Exponents are natural numbers (including zero), not arbitrary signed integers.
The all-ones-vector orbit, small-defect sixth-order identity and full R remain
outside these results. See `ReferenceMomentComparison_SCOPE.md`.
