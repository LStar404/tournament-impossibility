import ActualHessianComplex
import RawScalingSynthesis
import ActualCoreTracePrimitive
import ActualResidualFrozenFactorization
import BinaryGraphActivityBound

/-! Actual doubly stochastic data and exact zero source for the existing core. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace BalancedRawData
open Matrix
open RawFormalMixedSpecialization
variable {m : ℕ}

def centeredComplex (M : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  ActualHessianComplex.realComplex (M-ActualHessianFinite.P m)

def block (M : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  FullWickSquarefreeCompatibility.block (centeredComplex M)

def realBlock (M : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  FullWickSquarefreeCompatibility.block (M-ActualHessianFinite.P m)

lemma cast_realBlock (M : Matrix (Fin m) (Fin m) ℝ) :
    ActualHessianComplex.realComplex (realBlock M)=block M := by
  ext i j
  cases i <;> cases j <;> rfl

lemma real_rows (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    (hr : ∀ i, (∑ j, M i j)=1) (i : Fin m) :
    (∑ j, (M-ActualHessianFinite.P m) i j)=0 := by
  have hm0 : (m : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib]
  rw [hr i]
  simp [ActualHessianFinite.P, hm0]

lemma real_cols (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    (hc : ∀ j, (∑ i, M i j)=1) (j : Fin m) :
    (∑ i, (M-ActualHessianFinite.P m) i j)=0 := by
  have hm0 : (m : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib]
  rw [hc j]
  simp [ActualHessianFinite.P, hm0]

lemma rows (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    (hr : ∀ i, (∑ j, M i j)=1) (i : Fin m) :
    (∑ j, centeredComplex M i j)=0 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (real_rows hm M hr i)
  simpa [centeredComplex, ActualHessianComplex.realComplex] using h

lemma cols (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    (hc : ∀ j, (∑ i, M i j)=1) (j : Fin m) :
    (∑ i, centeredComplex M i j)=0 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (real_cols hm M hc j)
  simpa [centeredComplex, ActualHessianComplex.realComplex] using h

lemma entry (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ) {C : ℝ}
    (hM : ∀ i j, 0≤M i j) (hd : ∀ i j, M i j≤C/(m : ℝ)) (i j : Fin m) :
    ‖centeredComplex M i j‖≤(C+1)/(m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  change ‖((M i j-1/(m : ℝ) : ℝ) : ℂ)‖≤_
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |M i j|+|1/(m : ℝ)| := abs_sub _ _
    _ ≤ C/(m : ℝ)+1/(m : ℝ) := by
      apply add_le_add
      · simpa only [abs_of_nonneg (hM i j)] using hd i j
      · rw [abs_of_pos (one_div_pos.mpr hmR)]
    _ = _ := by ring

lemma transpose_eq_adjoint (M : Matrix (Fin m) (Fin m) ℝ) :
    (centeredComplex M).transpose=(centeredComplex M)ᴴ := by
  ext i j
  simp [centeredComplex, ActualHessianComplex.realComplex,
    Matrix.conjTranspose_apply, Matrix.transpose_apply]

lemma block_entry (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ) {C : ℝ}
    (hC : 0≤C) (hM : ∀ i j, 0≤M i j) (hd : ∀ i j, M i j≤C/(m : ℝ))
    (i j : Fin m ⊕ Fin m) : ‖block M i j‖≤(C+1)/(m : ℝ) := by
  have hn : 0≤(C+1)/(m : ℝ) := by positivity
  rw [block, BinaryGraphActivityBound.block_eq]
  cases i <;> cases j
  · simpa [BipartiteOperatorBound.block] using hn
  · simpa [BipartiteOperatorBound.block] using entry hm M hM hd _ _
  · simpa [BipartiteOperatorBound.block, Matrix.transpose_apply] using entry hm M hM hd _ _
  · simpa [BipartiteOperatorBound.block] using hn

lemma block_norm (M : Matrix (Fin m) (Fin m) ℝ) {q : ℝ} (hq : 0≤q)
    (hN : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M-ActualHessianFinite.P m)‖≤q) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (block M)‖≤q := by
  rw [block, BinaryGraphActivityBound.block_eq, transpose_eq_adjoint]
  apply BalancedHessianInverse.centered_block_gap _ hq
  exact ActualHessianComplex.realComplex_gap _ hq hN

lemma real_block_norm (M : Matrix (Fin m) (Fin m) ℝ) {q : ℝ} (hq : 0≤q)
    (hN : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M-ActualHessianFinite.P m)‖≤q) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (realBlock M)‖≤q := by
  apply RawScalingSynthesis.real_gap_of_complex _ hq
  rw [cast_realBlock]
  exact block_norm M hq hN

lemma block_one_zero (N : Matrix (Fin m) (Fin m) ℂ)
    (hr : ∀ i, (∑ j, N i j)=0) (hc : ∀ j, (∑ i, N i j)=0) :
    Matrix.mulVec (FullWickSquarefreeCompatibility.block N) (fun _ => 1)=0 := by
  rw [BinaryGraphActivityBound.block_eq]
  ext x
  cases x <;>
    simp [BipartiteOperatorBound.block, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.transpose_apply, hr, hc]

lemma block_mulVec_one_zero (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    (hr : ∀ i, (∑ j, M i j)=1) (hc : ∀ j, (∑ i, M i j)=1) :
    (block M).mulVec (fun _ => 1)=0 :=
  block_one_zero (centeredComplex M) (rows hm M hr) (cols hm M hc)

lemma mean_zero_of_mulVec_one_zero {I : Type*} [Fintype I]
    (Q : I → I → ℂ) (hQ : Matrix.mulVec Q (fun _ => 1)=0) :
    PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1)=0 := by
  have hconst : (MixedCovarianceSymmetry.constantMatrix Q).mulVec
      (fun _ => (1 : PowerSeries ℂ))=0 := by
    funext i
    change ((MixedCovarianceSymmetry.constantMatrix Q).mulVec
      (fun _ => (1 : PowerSeries ℂ))) i = (0 : PowerSeries ℂ)
    have hi : (∑ j, Q i j)=0 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hQ i
    simp only [Matrix.mulVec, dotProduct, MixedCovarianceSymmetry.constantMatrix,
      Matrix.of_apply, mul_one]
    rw [← map_sum, hi, map_zero]
  simp only [PhysicalTiltedCovariance.mean, PhysicalTiltedCovariance.covariance, map_one]
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hconst, Matrix.mulVec_zero, smul_zero]

lemma source_zero_of_mulVec_one_zero {I : Type*} [Fintype I]
    (Q : I → I → ℂ) (hQ : Matrix.mulVec Q (fun _ => 1)=0) :
    MixedEvenCandidate.source Q identityInteraction (fun _ => 1)=0 := by
  rw [ActualCoreTracePrimitive.source_eq_half_mean,
    mean_zero_of_mulVec_one_zero Q hQ]
  simp

/-- Formal identity for the old core; no analytic evaluation or sign claim. -/
theorem core_eq_branch_of_balanced (N : Matrix (Fin m) (Fin m) ℂ)
    (hr : ∀ i, (∑ j, N i j)=0) (hc : ∀ j, (∑ i, N i j)=0) :
    ActualResidualFrozenFactorization.core N =
      MixedEvenCandidate.branch (FullWickSquarefreeCompatibility.block N) identityInteraction := by
  rw [ActualResidualFrozenFactorization.core_formula, MixedEvenCandidate.candidate,
    source_zero_of_mulVec_one_zero _ (block_one_zero N hr hc)]
  change MixedEvenCandidate.branch _ _ * ZeroConstantFormalExp.expOf 0 = _
  rw [ZeroConstantFormalExp.zero, mul_one]

/-- Exact specialization to the actual centered doubly stochastic matrix. -/
theorem actual_core_eq_branch (hm : 0 < m) (M : Matrix (Fin m) (Fin m) ℝ)
    (hr : ∀ i, (∑ j, M i j)=1) (hc : ∀ j, (∑ i, M i j)=1) :
    ActualResidualFrozenFactorization.core (centeredComplex M) =
      MixedEvenCandidate.branch (block M) identityInteraction :=
  core_eq_branch_of_balanced (centeredComplex M) (rows hm M hr) (cols hm M hc)

end BalancedRawData
#check @BalancedRawData.block_norm
#print axioms BalancedRawData.block_norm
#check @BalancedRawData.block_mulVec_one_zero
#print axioms BalancedRawData.block_mulVec_one_zero
#check @BalancedRawData.mean_zero_of_mulVec_one_zero
#print axioms BalancedRawData.mean_zero_of_mulVec_one_zero
#check @BalancedRawData.source_zero_of_mulVec_one_zero
#print axioms BalancedRawData.source_zero_of_mulVec_one_zero
#check @BalancedRawData.core_eq_branch_of_balanced
#print axioms BalancedRawData.core_eq_branch_of_balanced
#check @BalancedRawData.actual_core_eq_branch
#print axioms BalancedRawData.actual_core_eq_branch
#check @BalancedRawData.real_block_norm
#print axioms BalancedRawData.real_block_norm
