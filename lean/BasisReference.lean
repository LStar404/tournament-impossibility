import TournamentPowerComparison
noncomputable section
namespace BasisReference
open TournamentPowerComparison TournamentSwitching

lemma first_basis_sorted (n : ℕ) (hn : 0 < n) :
    absSort (basis (⟨0,hn⟩ : Fin n)) = Equiv.refl (Fin n) := by
  unfold absSort
  apply Tuple.sort_eq_refl_iff_monotone.mpr
  intro i j hij
  by_cases hi : i = (⟨0,hn⟩ : Fin n)
  · by_cases hj : j = (⟨0,hn⟩ : Fin n)
    · simp [basis, Pi.single_apply, hi, hj]
    · simp [basis, Pi.single_apply, hi, hj]
  · have hj : j ≠ (⟨0,hn⟩ : Fin n) := by
      intro he
      have hijval : i.val ≤ j.val := hij
      have hjval : j.val = 0 := congrArg Fin.val he
      have hval : i.val ≤ 0 := by omega
      apply hi
      exact Fin.ext (Nat.eq_zero_of_le_zero hval)
    simp [basis, Pi.single_apply, hi, hj]

lemma sortedPad_basis_restrict (n : ℕ) (hn : 0 < n) (i : Fin n) :
    sortedPad (basis (⟨0,hn⟩ : Fin n)) i.val = basis (⟨0,hn⟩ : Fin n) i := by
  simp only [sortedPad, dif_pos i.isLt, first_basis_sorted]
  simp [basis, Pi.single_apply]
  split_ifs <;> norm_num
end BasisReference
#print axioms BasisReference.sortedPad_basis_restrict
