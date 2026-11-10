import ActualRecoveryUpperCandidate
set_option autoImplicit false
noncomputable section
namespace PhysicalMinorRecoveryCandidate
open Matrix Finset TournamentHamiltonian ActualTournamentPrescalingBounds
open MatrixScalingMassPotential NonprincipalReconstructionCandidate
open ActualReconstructionBridgeCandidate ActualKappaBridgeCandidate ActualControlledReconstructionCandidate
open ActualPrescalingNormalization DeletedScalingSynthesisCandidate ActualRecoveryUpperCandidate
variable {n m : ℕ}
def shiftedPotential (T : Tournament n) (I J : Finset (Fin n)) (x y : Fin m → ℝ) : ℝ :=
  let s := (m:ℝ)/((m:ℝ)+IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J)
  theta (fun i => x i+Real.log s/2) (fun j => y j+Real.log s/2)
def base (m : ℕ) : ℝ := (m.factorial:ℝ)/(m:ℝ)^m
lemma base_pos (hm : 0 < m) : 0<base m := by
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  unfold base
  positivity
lemma exact_same_root (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (C ε q : ℝ) (x y : Fin m → ℝ)
    (hw : reconstructedWitness T I J r c C ε q x y) :
    ((ActualReconstructionBridgeCandidate.adjacency T).submatrix (complementEmbedding I r) (complementEmbedding J c)).permanent =
      recoveryFactor T I J m * Real.exp (-shiftedPotential T I J x y) *
      (expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent := by
  exact hw.2.2.2.2.2
/-- Exact potential is retained on both the main term and error. The normalized
error premise is an interface to the separately proved same-root p=0 theorem. -/
theorem two_sided_transfer (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (hn : 2≤n) (hm : 0 < m) {a0 : ℝ} (h0 : 0≤a0) (h1 : a0<1)
    (ha : ∀ i,|normalizedScore T i|≤a0)
    (C ε q : ℝ) (x y : Fin m → ℝ)
    (hw : reconstructedWitness T I J r c C ε q x y)
    (G E : ℝ)
    (herror : |(expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent/base m-G|≤E) :
    |((ActualReconstructionBridgeCandidate.adjacency T).submatrix (complementEmbedding I r) (complementEmbedding J c)).permanent -
      recoveryFactor T I J m * Real.exp (-shiftedPotential T I J x y) * base m * G| ≤
      recoveryFactor T I J m * Real.exp (-shiftedPotential T I J x y) * base m * E := by
  have hb := base_pos hm
  have hR := recoveryFactor_nonnegative T I J m hn h0 h1 ha
  have hfac : 0≤recoveryFactor T I J m*Real.exp (-shiftedPotential T I J x y)*base m :=
    mul_nonneg (mul_nonneg hR (Real.exp_pos _).le) hb.le
  rw [exact_same_root T I J r c C ε q x y hw]
  calc
    _ = |(recoveryFactor T I J m*Real.exp (-shiftedPotential T I J x y)*base m)*
      ((expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent/base m-G)| := by
      congr 1
      field_simp [ne_of_gt hb]
      <;> ring
    _ = (recoveryFactor T I J m*Real.exp (-shiftedPotential T I J x y)*base m)*
      |(expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent/base m-G| := by rw [abs_mul, abs_of_nonneg hfac]
    _ ≤ _ := mul_le_mul_of_nonneg_left herror hfac
/-- The κ replacement is used only for a one-sided upper bound. -/
theorem upper_transfer (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (hn : 2≤n) (hm : 0 < m) {a0 : ℝ} (h0 : 0≤a0) (h1 : a0<1)
    (ha : ∀ i,|normalizedScore T i|≤a0)
    (C ε q : ℝ) (x y : Fin m → ℝ)
    (hw : reconstructedWitness T I J r c C ε q x y)
    (G E : ℝ)
    (herror : |(expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent/base m-G|≤E) :
    ((ActualReconstructionBridgeCandidate.adjacency T).submatrix (complementEmbedding I r) (complementEmbedding J c)).permanent ≤
      recoveryFactor T I J m * Real.exp (IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J)*base m*(G+E) := by
  have hb := base_pos hm
  have hper : (expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent ≤ base m*(G+E) := by
    have hh := (abs_le.mp herror).2
    have hh' : (expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent/base m≤G+E := by linarith
    have hh'' := (div_le_iff₀ hb).mp hh'
    simpa only [mul_comm] using hh''
  have hR := recoveryFactor_nonnegative T I J m hn h0 h1 ha
  calc
    _ ≤ _ := same_root_permanent_upper T I J r c hn h0 h1 ha C ε q x y hw
    _ ≤ recoveryFactor T I J m * Real.exp (IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J)*(base m*(G+E)) :=
      mul_le_mul_of_nonneg_left hper (mul_nonneg hR (Real.exp_pos _).le)
    _ = _ := by ring
end PhysicalMinorRecoveryCandidate
#check PhysicalMinorRecoveryCandidate.shiftedPotential
#print axioms PhysicalMinorRecoveryCandidate.shiftedPotential
#check PhysicalMinorRecoveryCandidate.base
#print axioms PhysicalMinorRecoveryCandidate.base
#check PhysicalMinorRecoveryCandidate.base_pos
#print axioms PhysicalMinorRecoveryCandidate.base_pos
#check PhysicalMinorRecoveryCandidate.exact_same_root
#print axioms PhysicalMinorRecoveryCandidate.exact_same_root
#check PhysicalMinorRecoveryCandidate.two_sided_transfer
#print axioms PhysicalMinorRecoveryCandidate.two_sided_transfer
#check PhysicalMinorRecoveryCandidate.upper_transfer
#print axioms PhysicalMinorRecoveryCandidate.upper_transfer
