# Repeated occurrence labels: focused verified scope

Finite occurrence-pairing modules; complete verification evidence is recorded in verification/result.json.

RepeatedLabelPairing.moment is a sum over ALL perfect pairings of 2n
OCCURRENCE POSITIONS (Fin n ⊕ Fin n), with covariance pulled back along an
arbitrary label map. The label map is NOT required to be injective; two
occurrences with the same coordinate remain separate positions. No term is
assigned the desired moment value by definition.

For symmetric covariance and zero monochromatic blocks of the selected
labels, moment_eq_permanent follows from the full positional pairing theorem.
color_permutation_invariant proves invariance under arbitrary separate
permutations of the left and right occurrence positions, using actual row/
column permutation invariance. repeated_four proves X^2 Y^2 gives 2*Cxy^2
when Cxx=Cyy=0. identity_labels identifies the same full pairing sum as the
already checked positional squarefree covariance theorem. This is compatibility
of those finite sums, not a full polynomial-functional extension theorem.

FullFourthMoment explicitly enumerates the three fixed-point-free involutions
on four positions, using kernel `decide` proofs for completeness and their
unique edge representatives (not native_decide). Expanding the actual sum
proves the complete three-term fourth-moment formula WITHOUT any zero-diagonal
assumption. In particular repeated_xxyy gives
  Cxx*Cyy + 2*Cxy^2.
This demonstrates that repeated-label contributions survive, unlike the earlier
squarefree coefficient projection. All reported endpoint axioms are only
propext, Classical.choice, Quot.sound; no sorryAx. Both candidates generated
oleans by focused compilation.

Limits: the present moment is indexed by an even number 2n of positions.
General odd-position definitions/vanishing, arbitrary position-reordering
invariance (including colour mixing), a general deletion recursion, the
Occ(d) extension to all polynomial monomials, and proof of its full squarefree
functional compatibility remain open. No Gaussian probability expectation,
linear/quadratic formal exponential re-summation, analytic recovery error,
or Condition R is claimed. The fourth-order formula alone does not prove
an all-orders Wick theorem.
