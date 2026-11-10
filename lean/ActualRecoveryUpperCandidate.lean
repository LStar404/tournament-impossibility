import ActualControlledReconstructionCandidate
set_option autoImplicit false
noncomputable section
namespace ActualRecoveryUpperCandidate
open Matrix Finset TournamentHamiltonian ActualTournamentPrescalingBounds
open MatrixScalingMassPotential NonprincipalReconstructionCandidate
open ActualReconstructionBridgeCandidate ActualKappaBridgeCandidate ActualControlledReconstructionCandidate
open ActualPrescalingNormalization DeletedScalingSynthesisCandidate
variable {n m : ℕ}
def recoveryFactor (T : Tournament n) (I J : Finset (Fin n)) (m : ℕ) : ℝ :=
  gamma (normalizedScore T)*(∏ i ∈ I,(1+normalizedScore T i)⁻¹)*
    (∏ j ∈ J,(1-normalizedScore T j)⁻¹)*
    ((m:ℝ)*((n:ℝ)-1)*((n:ℝ)+ActualPrescalingNormalization.nu T)/(2*(n:ℝ)^2))^m
lemma recoveryFactor_nonnegative (T : Tournament n) (I J : Finset (Fin n)) (m : ℕ)
    (hn : 2≤n) {a0 : ℝ} (h0 : 0≤a0) (h1 : a0<1)
    (ha : ∀ i,|normalizedScore T i|≤a0) : 0≤recoveryFactor T I J m := by
  have hab i : -1<normalizedScore T i ∧ normalizedScore T i<1 :=
    abs_lt.mp ((ha i).trans_lt h1)
  have hg : 0≤gamma (normalizedScore T) := by
    apply Finset.prod_nonneg
    intro i hi
    have hh := hab i
    nlinarith [sq_nonneg (normalizedScore T i)]
  have hp : 0≤∏ i ∈ I,(1+normalizedScore T i)⁻¹ := by
    apply Finset.prod_nonneg
    intro i hi
    apply inv_nonneg.mpr
    linarith [(hab i).1]
  have hm : 0≤∏ j ∈ J,(1-normalizedScore T j)⁻¹ := by
    apply Finset.prod_nonneg
    intro j hj
    apply inv_nonneg.mpr
    linarith [(hab j).2]
  have ht := total_pos T hn h0 h1 ha
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  unfold recoveryFactor
  apply mul_nonneg (mul_nonneg (mul_nonneg hg hp) hm)
  apply pow_nonneg
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (by linarith)) ht.le
  · positivity

theorem same_root_permanent_upper (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (hn : 2≤n) {a0 : ℝ} (h0 : 0≤a0) (h1 : a0<1)
    (ha : ∀ i,|normalizedScore T i|≤a0)
    (C ε q : ℝ) (x y : Fin m → ℝ)
    (hw : reconstructedWitness T I J r c C ε q x y) :
    ((ActualReconstructionBridgeCandidate.adjacency T).submatrix (complementEmbedding I r) (complementEmbedding J c)).permanent ≤
      recoveryFactor T I J m *
      Real.exp (IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J)*
      (expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent := by
  obtain ⟨hc,heq,hr,hg,hθ,hident⟩ := hw
  rw [hident]
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
      (recoveryFactor_nonnegative T I J m hn h0 h1 ha)
  · apply DiagonalScalingPermanent.permanent_nonneg
    intro i j
    exact (hc.2.2.2.2.1 i j).1
end ActualRecoveryUpperCandidate
#print axioms ActualRecoveryUpperCandidate.recoveryFactor
#check ActualRecoveryUpperCandidate.recoveryFactor
#print axioms ActualRecoveryUpperCandidate.recoveryFactor_nonnegative
#check ActualRecoveryUpperCandidate.recoveryFactor_nonnegative
#print axioms ActualRecoveryUpperCandidate.same_root_permanent_upper
#check ActualRecoveryUpperCandidate.same_root_permanent_upper
