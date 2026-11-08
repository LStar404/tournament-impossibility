import SelectedTournamentMajorization
open Finset

/-- Independent expanded check: the only assumptions are the actual matrix
entry conditions. No abstract extremal sequence or comparison is assumed. -/
theorem actual_matrix_prefix_endpoint (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hskew : ∀ i j, A i j = - A j i)
    (hunit : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1)
    (x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ range k, TournamentSwitching.sortedPad (fun a => ∑ b, A a b * x b) i) ≤
      (k : ℝ) * (∑ i ∈ range n, TournamentSwitching.sortedPad x i) -
      ∑ j ∈ range k, (MajorizationCone.penalty j : ℝ) *
        TournamentSwitching.sortedPad x (n-k+j) := by
  exact SelectedTournamentMajorization.tournament_prefix_bound
    ⟨A, hskew, hunit⟩ x k hk

#print axioms actual_matrix_prefix_endpoint
#print axioms MajorizationCone.K_preserves_cone
#print axioms MajorizationCone.K_preserves_prefix_order
