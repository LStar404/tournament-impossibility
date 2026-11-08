import ReferenceMomentComparison
open Finset

/-- Expanded independent endpoint: only actual skew ±1 entries are assumed. -/
theorem actual_all_integer_moments (n r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i)
    (hunit : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1) :
    (∑ i : Fin n, ∑ j : Fin n, ((A^r) i j)^2) ≤
      ∑ i : Fin n, ∑ j : Fin n, ((TransitiveOrbit.T n ^ r) i j)^2 := by
  exact ReferenceMomentComparison.frobenius_all_powers n r ⟨A, hskew, hunit⟩

#print axioms actual_all_integer_moments
#print axioms SignedReferenceConjugacy.concrete_square_conjugacy
#print axioms ReferenceMomentComparison.reference_column_norm
