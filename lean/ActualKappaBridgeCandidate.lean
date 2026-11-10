import ActualReconstructionBridgeCandidate
set_option autoImplicit false
noncomputable section
namespace ActualKappaBridgeCandidate
open Matrix Finset TournamentHamiltonian MatrixScalingMassPotential
open ActualReconstructionBridgeCandidate
variable {n m : ℕ}
def complementEmbedding (I : Finset (Fin n)) (r : Fin m ≃ {i // i ∈ Iᶜ}) : Fin m ↪ Fin n :=
  ⟨fun i => (r i).val, fun _ _ h => r.injective (Subtype.ext h)⟩
lemma complement_card (I : Finset (Fin n)) (r : Fin m ≃ {i // i ∈ Iᶜ}) :
    (m:ℝ)=(n:ℝ)-I.card := by
  have h := Fintype.card_congr r
  simp only [Fintype.card_fin, Fintype.card_coe, Finset.card_compl] at h
  rw [h, Nat.cast_sub (show I.card ≤ n by simpa using Finset.card_le_univ I)]
lemma physicalX_eq_reindexed (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ}) :
    physicalX T (complementEmbedding I r) (complementEmbedding J c) =
      (deletionMatrix (ActualPrescalingNormalization.normalizedMatrix T) I J).submatrix r c := by
  ext i j
  simp only [physicalX, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply,
    deletionMatrix, complementEmbedding]
  rw [complement_card I r]
  rfl
lemma kappa_reindex {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (A : Matrix ι κ ℝ) (r : α ≃ ι) (c : β ≃ κ) :
    kappa (A.submatrix r c)=kappa A := by
  unfold kappa totalMass
  simp only [Matrix.submatrix_apply]
  simp_rw [Equiv.sum_comp c]
  rw [Equiv.sum_comp r (fun i => ∑ j, A i j), Fintype.card_congr r]
lemma physicalX_kappa (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ}) :
    kappa (physicalX T (complementEmbedding I r) (complementEmbedding J c)) =
      IndependentDeletionMass.deletionExcess (ActualPrescalingNormalization.normalizedMatrix T) I J := by
  rw [physicalX_eq_reindexed, kappa_reindex, deletionMatrix_kappa]
lemma physicalX_nonnegative (T : Tournament n) (e f : Fin m ↪ Fin n)
    (hn : 2 ≤ n) {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |ActualTournamentPrescalingBounds.normalizedScore T i| ≤ a0) :
    ∀ i j, 0 ≤ physicalX T e f i j := by
  intro i j
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m))
    (ActualPrescalingNormalization.normalized_nonneg T hn h0 h1 ha (e i) (f j))
end ActualKappaBridgeCandidate

#print axioms ActualKappaBridgeCandidate.complementEmbedding
#check ActualKappaBridgeCandidate.complementEmbedding

#print axioms ActualKappaBridgeCandidate.complement_card
#check ActualKappaBridgeCandidate.complement_card

#print axioms ActualKappaBridgeCandidate.physicalX_eq_reindexed
#check ActualKappaBridgeCandidate.physicalX_eq_reindexed

#print axioms ActualKappaBridgeCandidate.kappa_reindex
#check ActualKappaBridgeCandidate.kappa_reindex

#print axioms ActualKappaBridgeCandidate.physicalX_kappa
#check ActualKappaBridgeCandidate.physicalX_kappa

#print axioms ActualKappaBridgeCandidate.physicalX_nonnegative
#check ActualKappaBridgeCandidate.physicalX_nonnegative
