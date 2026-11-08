import TournamentHamiltonian.PathConvolutionGenerating

namespace TournamentHamiltonian
open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

private def fixesOutside (s : Finset α) (σ : Equiv.Perm α) : Prop :=
  ∀ i, i ∉ s → σ i = i

omit [Fintype α] in
private theorem fixed_invariant (s : Finset α) (σ : Equiv.Perm α)
    (h : fixesOutside s σ) (i : α) : σ i ∈ s ↔ i ∈ s := by
  by_cases hi : i ∈ s
  · constructor
    · intro _; exact hi
    · intro _
      by_contra hn
      have he := h (σ i) hn
      have he' := σ.injective he
      exact hn (he'.symm ▸ hi)
  · rw [h i hi]

private noncomputable def fixedPermEquiv (s : Finset α) :
    Equiv.Perm s ≃ {σ : Equiv.Perm α // fixesOutside s σ} where
  toFun p := ⟨Equiv.Perm.ofSubtype p, fun i hi =>
    Equiv.Perm.ofSubtype_apply_of_not_mem p hi⟩
  invFun σ := σ.val.subtypePerm (fixed_invariant s σ.val σ.property)
  left_inv p := by
    ext i
    simp
  right_inv σ := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ s
    · simp [Equiv.Perm.ofSubtype_apply_of_mem, hi, Equiv.Perm.subtypePerm_apply]
    · simp [Equiv.Perm.ofSubtype_apply_of_not_mem, hi, σ.property i hi]

private theorem sum_fixed_products (A : Matrix α α ℝ) (s : Finset α) :
    (∑ σ : {σ : Equiv.Perm α // fixesOutside s σ}, ∏ i ∈ s, A (σ.val i) i) =
      (A.submatrix (Subtype.val : s → α) Subtype.val).permanent := by
  unfold Matrix.permanent
  symm
  apply Fintype.sum_equiv (fixedPermEquiv s)
  intro p
  rw [← Finset.prod_coe_sort s]
  apply Finset.prod_congr rfl
  intro i _
  simp [fixedPermEquiv, Matrix.submatrix_apply, Equiv.Perm.ofSubtype_apply_of_mem]

private theorem diagonal_product (σ : Equiv.Perm α) (s : Finset α) (v : ℝ) :
    (∏ i ∈ sᶜ, (Matrix.diagonal (fun _ : α => v)) (σ i) i) =
      if fixesOutside s σ then v ^ (sᶜ).card else 0 := by
  by_cases h : fixesOutside s σ
  · rw [ite_eq_left h]
    have he : (∏ i ∈ sᶜ, (Matrix.diagonal (fun _ : α => v)) (σ i) i) =
        ∏ _i ∈ sᶜ, v := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [h i (Finset.mem_compl.mp hi), Matrix.diagonal_apply_eq]
    rw [he, Finset.prod_const]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    have hh : i ∉ s ∧ σ i ≠ i := by simpa only [not_imp] using hi
    exact Finset.prod_eq_zero (Finset.mem_compl.mpr hh.1)
      (Matrix.diagonal_apply_ne _ hh.2)

/-- The actual permanent under a scalar diagonal perturbation; all dimensions,
including the empty matrix. -/
theorem permanent_add_diagonal_subsets (A : Matrix α α ℝ) (v : ℝ) :
    (A + Matrix.diagonal (fun _ : α => v)).permanent =
      ∑ s : Finset α, v ^ (sᶜ).card *
        (A.submatrix (Subtype.val : s → α) Subtype.val).permanent := by
  simp only [Matrix.permanent, Matrix.add_apply]
  simp_rw [Fintype.prod_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [diagonal_product]
  calc
    _ = v ^ (sᶜ).card * ∑ σ : Equiv.Perm α,
        if fixesOutside s σ then ∏ i ∈ s, A (σ i) i else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      split_ifs <;> ring
    _ = _ := by
      congr 1
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter (fixesOutside s)) (by simp) (fun σ : Equiv.Perm α => ∏ i ∈ s, A (σ i) i)).trans
        (sum_fixed_products A s)

theorem permanent_add_diagonal_complement (A : Matrix α α ℝ) (v : ℝ) :
    (A + Matrix.diagonal (fun _ : α => v)).permanent =
      ∑ U : Finset α, v ^ U.card *
        (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent := by
  rw [permanent_add_diagonal_subsets]
  apply Fintype.sum_equiv (⟨fun s : Finset α => sᶜ, fun s => sᶜ, compl_compl, compl_compl⟩ : Finset α ≃ Finset α)
  intro s
  change v ^ sᶜ.card * _ = v ^ sᶜ.card * _
  congr 1
  let e : ((sᶜ)ᶜ : Finset α) ≃ s := Equiv.subtypeEquivRight (fun i => by simp)
  exact (permanent_submatrix_equiv_self
    (A.submatrix (Subtype.val : s → α) Subtype.val) e).symm

/-- Averaging the plus and minus identity perturbations selects precisely
all even removed vertex subsets. -/
theorem permanent_two_branch_average (A : Matrix α α ℝ) :
    ((A + 1).permanent + (A - 1).permanent) / 2 =
      ∑ U : Finset α, if Even U.card then
        (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent else 0 := by
  have hp : A + 1 = A + Matrix.diagonal (fun _ : α => (1 : ℝ)) := by simp
  have hm : A - 1 = A + Matrix.diagonal (fun _ : α => (-1 : ℝ)) := by
    ext i j
    by_cases h : i = j <;> simp [h, sub_eq_add_neg]
  rw [hp, hm, permanent_add_diagonal_complement, permanent_add_diagonal_complement,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro U _
  by_cases h : Even U.card
  · simp [h, h.neg_one_pow]
  · simp [h, (Nat.not_even_iff_odd.mp h).neg_one_pow]

end TournamentHamiltonian
