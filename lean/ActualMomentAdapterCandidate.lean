import ReferenceMomentEndpoint
import TournamentHamiltonian.TransitiveDeterminant

/-!
Isolated candidate; see build/STATUS.json for compilation and audit evidence.
No sorry/admit/axiom. This only adapts the existing all-integer Frobenius
moment theorem to the Hamiltonian-path tournament representation.
It does not itself prove the spectral log-series or sharp path bound.
-/

open scoped BigOperators

namespace ActualMomentAdapterCandidate
open TournamentHamiltonian

/-- The two existing transitive sign conventions agree definitionally. -/
theorem transitiveOrbit_eq_signMatrix (n : ℕ) :
    TransitiveOrbit.T n = signMatrix (TournamentHamiltonian.transitiveTournament n) := by
  rw [signMatrix_transitiveTournament]
  rfl

/-- The existing universal all-power theorem applies to the actual Bool
orientation representation used by the Hamiltonian path endpoints. -/
theorem actual_frobenius_moments_le_transitive {n : ℕ}
    (T : Tournament n) (r : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, ((signMatrix T ^ r) i j) ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n,
        ((signMatrix (TournamentHamiltonian.transitiveTournament n) ^ r) i j) ^ 2 := by
  have hunit : ∀ i j : Fin n, i ≠ j →
      signMatrix T i j = 1 ∨ signMatrix T i j = -1 := by
    intro i j hij
    cases he : T.val i j <;> simp [signMatrix, hij, he]
  have h := actual_all_integer_moments n r (signMatrix T)
    (signMatrix_skew T) hunit
  rw [transitiveOrbit_eq_signMatrix] at h
  exact h

/-- The first relevant odd squared-frequency moment will use r=3. -/
theorem actual_frobenius_cube_le_transitive {n : ℕ} (T : Tournament n) :
    (∑ i : Fin n, ∑ j : Fin n, ((signMatrix T ^ 3) i j) ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n,
        ((signMatrix (TournamentHamiltonian.transitiveTournament n) ^ 3) i j) ^ 2 :=
  actual_frobenius_moments_le_transitive T 3

end ActualMomentAdapterCandidate

#print axioms ActualMomentAdapterCandidate.transitiveOrbit_eq_signMatrix
#print axioms ActualMomentAdapterCandidate.actual_frobenius_moments_le_transitive
#print axioms ActualMomentAdapterCandidate.actual_frobenius_cube_le_transitive
