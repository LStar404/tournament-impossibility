import NonprincipalReconstructionCandidate
import DeletedScalingSynthesisCandidate
set_option autoImplicit false
noncomputable section
namespace ActualReconstructionBridgeCandidate
open Matrix Finset TournamentHamiltonian ActualTournamentPrescalingBounds
open MatrixScalingMassPotential NonprincipalReconstructionCandidate
variable {n m : ℕ}

def adjacency (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (1-(if i=j then 1 else 0)+signMatrix T i j)/2

def physicalX (T : Tournament n) (e f : Fin m ↪ Fin n) : Matrix (Fin m) (Fin m) ℝ :=
  ((n:ℝ)/(m:ℝ)) • (ActualPrescalingNormalization.normalizedMatrix T).submatrix e f

lemma pre_eq_prescaled (T : Tournament n) :
    pre (adjacency T) (normalizedScore T)=prescaled T := by
  ext i j
  simp only [pre,adjacency,prescaled,scaled,baseMatrix,TournamentPrescalingMass.ell,TournamentPrescalingMass.rightScale]
  ring

lemma nu_eq_actual (T : Tournament n) :
    NonprincipalReconstructionCandidate.nu (adjacency T) (normalizedScore T)=ActualPrescalingNormalization.nu T := by
  unfold NonprincipalReconstructionCandidate.nu
  rw [pre_eq_prescaled,ActualPrescalingNormalization.prescaled_total]
  ring

lemma normalized_eq_actual (T : Tournament n) :
    normalizedPre (adjacency T) (normalizedScore T)=ActualPrescalingNormalization.normalizedMatrix T := by
  rw [normalizedPre,nu_eq_actual,pre_eq_prescaled]
  rfl

lemma deletedX_eq_physical (T : Tournament n) (e f : Fin m ↪ Fin n) :
    deletedX (adjacency T) (normalizedScore T) e f=physicalX T e f := by
  rw [deletedX,normalized_eq_actual]
  rfl

lemma actualDeleted_eq_scalar (T : Tournament n) (e f : Fin m ↪ Fin n)
    (I J : Finset (Fin n)) (hm : 0 < m) :
    DeletedScalingSynthesisCandidate.actualDeleted T e f I J =
      ((m:ℝ)/((m:ℝ)+IndependentDeletionMass.deletionExcess
        (ActualPrescalingNormalization.normalizedMatrix T) I J)) • physicalX T e f := by
  have hmR : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  ext i j
  simp only [DeletedScalingSynthesisCandidate.actualDeleted,DeletedScalingSynthesisCandidate.deleted,
    physicalX,Matrix.smul_apply,Matrix.submatrix_apply,smul_eq_mul]
  field_simp [hmR]

/-- The same actual Y root gives the same balanced matrix after transfer to X. -/
theorem actual_root_transfer (T : Tournament n) (e f : Fin m ↪ Fin n)
    (I J : Finset (Fin n)) (hm : 0 < m)
    (hk : 0<(m:ℝ)+IndependentDeletionMass.deletionExcess
      (ActualPrescalingNormalization.normalizedMatrix T) I J)
    (x y : Fin m → ℝ)
    (hroot : ActualRootEnergy.root (DeletedScalingSynthesisCandidate.actualDeleted T e f I J) x y) :
    let c := (m:ℝ)/((m:ℝ)+IndependentDeletionMass.deletionExcess
      (ActualPrescalingNormalization.normalizedMatrix T) I J)
    expScaled (physicalX T e f) (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2) =
      expScaled (DeletedScalingSynthesisCandidate.actualDeleted T e f I J) x y ∧
    ActualRootEnergy.root (physicalX T e f) (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2) ∧
    theta (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2)=theta x y+(m:ℝ)*Real.log c := by
  dsimp only
  let c := (m:ℝ)/((m:ℝ)+IndependentDeletionMass.deletionExcess (ActualPrescalingNormalization.normalizedMatrix T) I J)
  have hc : 0<c := div_pos (by exact_mod_cast hm) hk
  have heq : expScaled (physicalX T e f) (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2) =
      expScaled (DeletedScalingSynthesisCandidate.actualDeleted T e f I J) x y := by
    rw [positive_scalar_root_transfer _ c hc,actualDeleted_eq_scalar T e f I J hm]
  refine ⟨heq, ?_, positive_scalar_potential_transfer c x y⟩
  have hr : ∀ i,∑ j,expScaled (DeletedScalingSynthesisCandidate.actualDeleted T e f I J) x y i j=1 := by
    simpa [expScaled,mul_comm] using hroot.1
  have hcol : ∀ j,∑ i,expScaled (DeletedScalingSynthesisCandidate.actualDeleted T e f I J) x y i j=1 := by
    simpa [expScaled,mul_comm] using hroot.2
  rw [← heq] at hr hcol
  constructor
  · simpa [expScaled,mul_comm] using hr
  · simpa [expScaled,mul_comm] using hcol

/-- Actual tournament factors in the generic exact permanent reconstruction.
This is an exact identity, not a Gaussian or permanent asymptotic claim. -/
theorem actual_permanent_reconstruction (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (hn : 2≤n) (hm : 0 < m) {a0 : ℝ} (h0 : 0≤a0) (h1 : a0<1)
    (ha : ∀ i,|normalizedScore T i|≤a0) (x y : Fin m → ℝ) :
    let rr := fun i => (r i).val
    let cc := fun j => (c j).val
    ((adjacency T).submatrix rr cc).permanent =
      gamma (normalizedScore T)*(∏ i ∈ I,(1+normalizedScore T i)⁻¹)*
      (∏ j ∈ J,(1-normalizedScore T j)⁻¹)*
      ((m:ℝ)*((n:ℝ)-1)*((n:ℝ)+ActualPrescalingNormalization.nu T)/(2*(n:ℝ)^2))^m*
      Real.exp (-theta x y)*
      (expScaled (((n:ℝ)/(m:ℝ)) •
        (ActualPrescalingNormalization.normalizedMatrix T).submatrix rr cc) x y).permanent := by
  have hnu : (n:ℝ)+NonprincipalReconstructionCandidate.nu (adjacency T) (normalizedScore T)≠0 := by
    rw [nu_eq_actual]
    exact (ActualPrescalingNormalization.total_pos T hn h0 h1 ha).ne'
  have hh := exact_reconstruction (adjacency T) (normalizedScore T) I J r c (by omega) hm
    (fun i => lt_of_le_of_lt (ha i) h1) hnu x y
  simpa only [scale,nu_eq_actual,deletedX,normalized_eq_actual] using hh
open ActualHessianComplex ActualHessianFinite
open scoped Matrix.Norms.L2Operator
def controlledWitness (M : Matrix (Fin m) (Fin m) ℝ) (C ε q : ℝ)
    (x y : Fin m → ℝ) : Prop :=
  let a := RawScalingSynthesis.radius C q ε;
    ‖ActualRootEnergy.vector x y‖ ≤ a ∧
    (∑ i,x i) = ∑ j,y j ∧
    ActualRootEnergy.root M x y ∧
    FiniteSymmetricQuadratic.l2 (ActualRootEnergy.vector x y) ≤
      Real.exp (2*a)/(1-q-4*ε)*FiniteSymmetricQuadratic.l2 (ActualRootEnergy.residual M) ∧
    (∀ i j,0 ≤ expScaled M x y i j ∧ expScaled M x y i j ≤ Real.exp (2*a)*(C/(m:ℝ))) ∧
    (∑ i,∑ j,(expScaled M x y i j-M i j)^2) ≤
      (2*C*(1+ε)*Real.exp (4*a)/(m:ℝ))*(Real.exp (2*a)/(1-q-4*ε))^2*
        FiniteSymmetricQuadratic.energy (ActualRootEnergy.residual M) ∧
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (realComplex (expScaled M x y-P m))‖ ≤
      q+(1+ε)*(Real.exp (2*a)-1) ∧
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (realComplex (expScaled M x y-P m))‖ ≤ (1+q)/2 ∧
    (1+q)/2 < 1


/-- Use the exact same x,y supplied by the controlled actual Y construction. -/
theorem controlled_actual_root_transfer (T : Tournament n) (e f : Fin m ↪ Fin n)
    (I J : Finset (Fin n)) (hm : 0 < m)
    (hk : 0<(m:ℝ)+IndependentDeletionMass.deletionExcess
      (ActualPrescalingNormalization.normalizedMatrix T) I J)
    (C ε q : ℝ)
    (hctrl : DeletedScalingSynthesisCandidate.controlled
      (DeletedScalingSynthesisCandidate.actualDeleted T e f I J) C ε q)
    (hX : ∀ i j,0≤physicalX T e f i j) :
    let c := (m:ℝ)/((m:ℝ)+IndependentDeletionMass.deletionExcess
      (ActualPrescalingNormalization.normalizedMatrix T) I J)
    ∃ x y : Fin m → ℝ,
      controlledWitness (DeletedScalingSynthesisCandidate.actualDeleted T e f I J) C ε q x y ∧
      ActualRootEnergy.root (DeletedScalingSynthesisCandidate.actualDeleted T e f I J) x y ∧
      expScaled (physicalX T e f) (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2) =
        expScaled (DeletedScalingSynthesisCandidate.actualDeleted T e f I J) x y ∧
      ActualRootEnergy.root (physicalX T e f) (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2) ∧
      (∑ i,(x i+Real.log c/2))=(∑ j,(y j+Real.log c/2)) ∧
      -theta (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2)≤kappa (physicalX T e f) := by
  dsimp only
  let c := (m:ℝ)/((m:ℝ)+IndependentDeletionMass.deletionExcess (ActualPrescalingNormalization.normalizedMatrix T) I J)
  obtain ⟨x,y,hbound,hgauge,hroot,hrest⟩ := hctrl
  have ht := actual_root_transfer T e f I J hm hk x y hroot
  refine ⟨x,y,⟨hbound,hgauge,hroot,hrest⟩,hroot,ht.1,ht.2.1,?_,?_⟩
  · have hh := positive_scalar_gauge_transfer c x y
    linarith
  · have hrow : ∀ i,∑ j,expScaled (physicalX T e f) (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2) i j=1 := by
      simpa [expScaled,mul_comm] using ht.2.1.1
    have hcol : ∀ j,∑ i,expScaled (physicalX T e f) (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2) i j=1 := by
      simpa [expScaled,mul_comm] using ht.2.1.2
    have hh := theta_ge_neg_kappa (physicalX T e f) _ _ hX hrow hcol
    linarith
end ActualReconstructionBridgeCandidate

#print axioms ActualReconstructionBridgeCandidate.adjacency
#check ActualReconstructionBridgeCandidate.adjacency
#print axioms ActualReconstructionBridgeCandidate.physicalX
#check ActualReconstructionBridgeCandidate.physicalX
#print axioms ActualReconstructionBridgeCandidate.pre_eq_prescaled
#check ActualReconstructionBridgeCandidate.pre_eq_prescaled
#print axioms ActualReconstructionBridgeCandidate.nu_eq_actual
#check ActualReconstructionBridgeCandidate.nu_eq_actual
#print axioms ActualReconstructionBridgeCandidate.normalized_eq_actual
#check ActualReconstructionBridgeCandidate.normalized_eq_actual
#print axioms ActualReconstructionBridgeCandidate.deletedX_eq_physical
#check ActualReconstructionBridgeCandidate.deletedX_eq_physical
#print axioms ActualReconstructionBridgeCandidate.actualDeleted_eq_scalar
#check ActualReconstructionBridgeCandidate.actualDeleted_eq_scalar
#print axioms ActualReconstructionBridgeCandidate.actual_root_transfer
#check ActualReconstructionBridgeCandidate.actual_root_transfer
#print axioms ActualReconstructionBridgeCandidate.actual_permanent_reconstruction
#check ActualReconstructionBridgeCandidate.actual_permanent_reconstruction
#print axioms ActualReconstructionBridgeCandidate.controlledWitness
#check ActualReconstructionBridgeCandidate.controlledWitness
#print axioms ActualReconstructionBridgeCandidate.controlled_actual_root_transfer
#check ActualReconstructionBridgeCandidate.controlled_actual_root_transfer
