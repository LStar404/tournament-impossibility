import TournamentHamiltonian.FourBlockPermanent
set_option autoImplicit false
noncomputable section
namespace InducedSelectedAdapter
open TournamentHamiltonian
open scoped Classical
variable {n : ℕ}
def localSet (M I : Finset (Fin n)) : Finset (Fin M.card) :=
  Finset.univ.filter (fun i => (subsetVertexEquiv M i).val ∈ I)
def localEquiv (M I : Finset (Fin n)) (hIM : I ⊆ M) : localSet M I ≃ I where
  toFun i := ⟨(subsetVertexEquiv M i.val).val, by simpa [localSet] using i.property⟩
  invFun i := ⟨(subsetVertexEquiv M).symm ⟨i.val,hIM i.property⟩, by simp [localSet]⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv i := by apply Subtype.ext; simp
lemma localSet_card (M I : Finset (Fin n)) (hIM : I ⊆ M) :
    (localSet M I).card = I.card := by
  simpa using Fintype.card_congr (localEquiv M I hIM)
def retainedEquiv (M I : Finset (Fin n)) : ↥((localSet M I)ᶜ) ≃ ↥(M \ I) where
  toFun i := ⟨(subsetVertexEquiv M i.val).val, by
    have hi : (subsetVertexEquiv M i.val).val ∉ I := by simpa [localSet] using i.property
    exact Finset.mem_sdiff.mpr ⟨(subsetVertexEquiv M i.val).property,hi⟩⟩
  invFun i := ⟨(subsetVertexEquiv M).symm ⟨i.val,(Finset.mem_sdiff.mp i.property).1⟩, by
    have hi := (Finset.mem_sdiff.mp i.property).2
    simpa [localSet] using hi⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv i := by apply Subtype.ext; simp
lemma selected_induced_eq (T : Tournament n) (M I J : Finset (Fin n)) :
    selectedPermanent (adjacency (inducedTournament T M)) (localSet M J)ᶜ (localSet M I)ᶜ =
      selectedPermanent (adjacency T) (M \ J) (M \ I) := by
  exact rectangularPermanent_submatrix_equiv
    (fun (i : ↥(M \ I)) (j : ↥(M \ J)) => adjacency T i j)
    (retainedEquiv M J) (retainedEquiv M I)
lemma local_weight_product (M I : Finset (Fin n)) (hIM : I ⊆ M) (w : Fin n → ℝ) :
    (∏ i ∈ localSet M I, w (subsetVertexEquiv M i)) = ∏ i ∈ I, w i := by
  have h := Fintype.prod_equiv (localEquiv M I hIM)
    (fun i => w (subsetVertexEquiv M i.val)) (fun i => w i.val) (fun _ => rfl)
  rw [Finset.prod_coe_sort (localSet M I) (fun i => w (subsetVertexEquiv M i)),
    Finset.prod_coe_sort I w] at h
  exact h
lemma common_threshold {n N K : ℕ} (hn : 2*K ≤ n) (hN : (n:ℝ)/2 ≤ N) : K ≤ N := by
  have hk : (2:ℝ)*K ≤ n := by exact_mod_cast hn
  have hh : (K:ℝ) ≤ N := by linarith
  exact_mod_cast hh
end InducedSelectedAdapter
