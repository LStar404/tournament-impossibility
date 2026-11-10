import ProjectedTwoColorWoodbury
import BipartiteOperatorBound
import PermanentCircleActualCentering
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
FORMAL-NAME SHARED SOURCE. Focused verification evidence: focused/result.json.
The frozen 378 source tree is unchanged.
The numerical disk is genuine: n >= 24, real skew entries bounded by 1,
real |v| <= 1, and |z| <= 5/4. No score or target-error hypothesis is used
for invertibility. No entrywise O(n^-3) claim is made.
-/
noncomputable section
namespace ProjectedTournamentDisk
open Matrix RawFourBlockResolvent ProjectedTwoColorWoodbury
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The projected normalized one-color branch, with the genuine Pi. -/
def branch (S : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (n:ℂ)⁻¹ • (ComplexifiedSkewBound.complexify S+(v:ℂ) • projection n)

def rawInteraction (S : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (n:ℂ)⁻¹ • RawFourBlockResolvent.interaction
    (ComplexifiedSkewBound.complexify S) (v:ℂ)

def projectedInteraction (S : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (n:ℂ)⁻¹ • ProjectedTwoColorWoodbury.projectedInteraction
    (ComplexifiedSkewBound.complexify S) (v:ℂ)

lemma complexify_skew (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) :
    (ComplexifiedSkewBound.complexify S).transpose=
      -ComplexifiedSkewBound.complexify S := by
  ext i j
  change (S j i : ℂ) = -(S i j : ℂ)
  exact_mod_cast hS i j

/-- The existing skew margin is unchanged because Pi is an orthogonal
projection and therefore has Euclidean operator norm at most one. -/
theorem branch_bound (hn : 24 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (v : ℝ) (hv : |v| ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (branch S v)‖ ≤ 3/4 := by
  have hnR : (24:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hu := TournamentSkewMargin.unnormalized S hS he
  have hi : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (projection n)‖ ≤ 1 :=
    PermanentSpectralFrame.complement_op_norm_le_one (by omega)
  have hs : ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
      (ComplexifiedSkewBound.complexify S+(v:ℂ) • projection n)‖ ≤
      (n:ℝ)*(17/24)+1 := by
    rw [map_add,map_smul]
    exact (norm_add_le _ _).trans (add_le_add hu (by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hi (abs_nonneg v)).trans (by simpa using hv)))
  unfold branch
  rw [map_smul,norm_smul,norm_inv,Complex.norm_natCast]
  have hb := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (le_of_lt hn0))
  apply hb.trans
  have hiN : (n:ℝ)⁻¹ ≤ 1/24 := by
    exact (inv_le_comm₀ hn0 (by norm_num)).mpr (by norm_num; exact hn)
  have hid : (n:ℝ)⁻¹*(n:ℝ)=1 := inv_mul_cancel₀ (ne_of_gt hn0)
  nlinarith

lemma branch_transpose (S : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) :
    (branch S v).transpose=branch S.transpose v := by
  simp only [branch,Matrix.transpose_smul,Matrix.transpose_add,
    projection_transpose]
  rfl

lemma projectedInteraction_eq_block (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (v : ℝ) :
    projectedInteraction S v=
      BipartiteOperatorBound.block (branch S v) (branch S.transpose v) := by
  have hC : ComplexifiedSkewBound.complexify S.transpose=
      -ComplexifiedSkewBound.complexify S := complexify_skew S hS
  unfold projectedInteraction ProjectedTwoColorWoodbury.projectedInteraction
    BipartiteOperatorBound.block
  rw [Matrix.fromBlocks_smul]
  simp only [smul_zero,branch,hC]

lemma rawInteraction_eq_block (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (v : ℝ) :
    rawInteraction S v=BipartiteOperatorBound.block
      (TournamentSkewMargin.branch S v) (TournamentSkewMargin.branch S v).transpose := by
  unfold rawInteraction RawFourBlockResolvent.interaction
    BipartiteOperatorBound.block TournamentSkewMargin.branch
  rw [Matrix.fromBlocks_smul]
  simp only [smul_zero,Matrix.transpose_smul,Matrix.transpose_add,
    Matrix.transpose_one,complexify_skew S hS]

theorem projectedInteraction_bound (hn : 24 ≤ n)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (v : ℝ) (hv : |v| ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (projectedInteraction S v)‖ ≤ 3/4 := by
  rw [projectedInteraction_eq_block S hS v]
  exact BipartiteOperatorBound.bound _ _ _ (by norm_num)
    (branch_bound hn S hS he v hv)
    (branch_bound hn S.transpose (fun i j => hS j i) (fun i j => he j i) v hv)

lemma rawSystem_eq_affine (S : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) (z : ℂ) :
    system (ComplexifiedSkewBound.complexify S) (z*(n:ℂ)⁻¹)
      ((z*(n:ℂ)⁻¹)*(v:ℂ))=1+z • rawInteraction S v := by
  rw [← RawFourBlockResolvent.actual_eq_system]
  simp only [AffineMatrixTaylorBridge.actual,rawInteraction,smul_smul]

lemma projectedSystem_eq_affine (S : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) (z : ℂ) :
    projectedSystem (ComplexifiedSkewBound.complexify S) (z*(n:ℂ)⁻¹)
      ((z*(n:ℂ)⁻¹)*(v:ℂ))=1+z • projectedInteraction S v := by
  rw [← ProjectedTwoColorWoodbury.actual_eq_projectedSystem]
  simp only [AffineMatrixTaylorBridge.actual,projectedInteraction,smul_smul]

/-- Fixed origin-centered complex disk; the source scores are unrestricted. -/
theorem raw_inverse_disk (hn : 24 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (v : ℝ) (hv : |v| ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 5/4) :
    IsUnit (system (ComplexifiedSkewBound.complexify S) (z*(n:ℂ)⁻¹)
      ((z*(n:ℂ)⁻¹)*(v:ℂ))) ∧
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
      ((system (ComplexifiedSkewBound.complexify S) (z*(n:ℂ)⁻¹)
        ((z*(n:ℂ)⁻¹)*(v:ℂ)))⁻¹)‖ ≤ 16 := by
  rw [rawSystem_eq_affine]
  have hq : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (rawInteraction S v)‖ ≤ 3/4 := by
    rw [rawInteraction_eq_block S hS v]
    exact BipartiteOperatorBound.tournament_bound hn S hS he v hv
  have h := RawBlockNeumannInverse.inverse_bound (rawInteraction S v) z
    (s:=5/4) (q:=3/4) hz hq (by norm_num)
  norm_num at h ⊢
  exact h

/-- The same bound for the actual Pi-projected matrix. No invertibility input. -/
theorem projected_inverse_disk (hn : 24 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (v : ℝ) (hv : |v| ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 5/4) :
    IsUnit (projectedSystem (ComplexifiedSkewBound.complexify S) (z*(n:ℂ)⁻¹)
      ((z*(n:ℂ)⁻¹)*(v:ℂ))) ∧
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
      ((projectedSystem (ComplexifiedSkewBound.complexify S) (z*(n:ℂ)⁻¹)
        ((z*(n:ℂ)⁻¹)*(v:ℂ)))⁻¹)‖ ≤ 16 := by
  rw [projectedSystem_eq_affine]
  have h := RawBlockNeumannInverse.inverse_bound (projectedInteraction S v) z
    (s:=5/4) (q:=3/4) hz (projectedInteraction_bound hn S hS he v hv) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Converse Schur transport, used only to discharge the finite interface. -/
lemma schur_isUnit_of_system (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ)
    (hM : IsUnit (system C f b)) : IsUnit (schur C f b) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hM
  simpa only [system,Matrix.det_fromBlocks_one₁₁,schur_eq] using hd

/-- Sylvester transport discharges G from two already established actual
inverses, rather than assuming a rank-two denominator bound. -/
lemma inner_isUnit_of_systems (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ)
    (hM : IsUnit (system C f b)) (hP : IsUnit (projectedSystem C f b)) :
    IsUnit (innerMatrix C f b) := by
  have hh : (system C f b)⁻¹*projectedSystem C f b=
      1+((system C f b)⁻¹*columns n)*rows n b := by
    rw [projected_eq_update,Matrix.mul_add,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)]
    simp only [Matrix.mul_assoc]
  have hu : IsUnit (1+((system C f b)⁻¹*columns n)*rows n b) := by
    rw [← hh]
    exact ((Matrix.isUnit_nonsing_inv_iff).mpr hM).mul hP
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [Matrix.det_one_add_mul_comm] at hd
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simpa only [innerMatrix,Matrix.mul_assoc] using hd

/-- Both formerly explicit finite-interface hypotheses now follow from the
real tournament bounds on the fixed complex disk. -/
theorem finite_interface_disk (hn : 24 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (v : ℝ) (hv : |v| ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 5/4) :
    IsUnit (schur (ComplexifiedSkewBound.complexify S) (z*(n:ℂ)⁻¹)
      ((z*(n:ℂ)⁻¹)*(v:ℂ))) ∧
    IsUnit (innerMatrix (ComplexifiedSkewBound.complexify S) (z*(n:ℂ)⁻¹)
      ((z*(n:ℂ)⁻¹)*(v:ℂ))) := by
  have hM := (raw_inverse_disk hn S hS he v hv z hz).1
  have hP := (projected_inverse_disk hn S hS he v hv z hz).1
  exact ⟨schur_isUnit_of_system _ _ _ hM,inner_isUnit_of_systems _ _ _ hM hP⟩

/-- The paper parameter t lies on a fixed disk around 1. The rescaled z
stays in the preceding origin-centered disk, uniformly in n and sigma. -/
theorem parameter_disk (hn : 24 ≤ n) (sigma : ℝ) (hsigma : |sigma| ≤ 1)
    (t : ℂ) (ht : ‖t-1‖ ≤ 1/8) :
    ‖t*(n:ℂ)/((n:ℂ)+(sigma:ℂ))‖ ≤ 5/4 := by
  have hnR : (24:ℝ) ≤ n := by exact_mod_cast hn
  have hsig := (abs_le.mp hsigma).1
  have hden : 0 < (n:ℝ)+sigma := by linarith
  have ht' : ‖t‖ ≤ 9/8 := by
    calc
      _ = ‖(t-1)+1‖ := by congr 1; ring
      _ ≤ ‖t-1‖+‖(1:ℂ)‖ := norm_add_le _ _
      _ ≤ 9/8 := by norm_num at *; linarith
  have hnC : (n:ℂ)+(sigma:ℂ)=(((n:ℝ)+sigma:ℝ):ℂ) := by simp
  rw [norm_div,norm_mul,Complex.norm_natCast,hnC,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have hh := mul_le_mul_of_nonneg_right ht' (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  nlinarith

lemma parameter_scale (hn : 0<n) (sigma : ℝ) (t : ℂ) :
    (t*(n:ℂ)/((n:ℂ)+(sigma:ℂ)))*(n:ℂ)⁻¹=
      t/((n:ℂ)+(sigma:ℂ)) := by
  have hnC : (n:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [div_eq_mul_inv]
  calc
    _ = (t*((n:ℂ)+(sigma:ℂ))⁻¹)*((n:ℂ)*(n:ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hnC,mul_one]

/-- Actual f=t/(n+sigma), b=f*sigma on a fixed disk around t=1.
The only input bounds are on tournament entries and sigma, not on inverses,
scores, the Woodbury denominator, or a desired projection error. -/
theorem actual_parameter_disk (hn : 24 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (sigma : ℝ) (hsigma : |sigma| ≤ 1) (t : ℂ) (ht : ‖t-1‖ ≤ 1/8) :
    let C := ComplexifiedSkewBound.complexify S
    let f := t/((n:ℂ)+(sigma:ℂ))
    IsUnit (schur C f (f*(sigma:ℂ))) ∧
    IsUnit (innerMatrix C f (f*(sigma:ℂ))) ∧
    IsUnit (projectedSystem C f (f*(sigma:ℂ))) ∧
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) ((projectedSystem C f (f*(sigma:ℂ)))⁻¹)‖ ≤ 16 := by
  dsimp only
  have hz := parameter_disk hn sigma hsigma t ht
  have hfinite := finite_interface_disk hn S hS he sigma hsigma
    (t*(n:ℂ)/((n:ℂ)+(sigma:ℂ))) hz
  have hprojected := projected_inverse_disk hn S hS he sigma hsigma
    (t*(n:ℂ)/((n:ℂ)+(sigma:ℂ))) hz
  rw [parameter_scale (by omega) sigma t] at hfinite hprojected
  exact ⟨hfinite.1,hfinite.2,hprojected⟩

/-- Pi annihilates constants exactly. Thus genuine projected source scores
are the raw scores of S divided by n, with opposite signs in the colors. -/
theorem projected_scores (hn : 0<n) (S : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) :
    (projectedInteraction S v).mulVec (fun _ => 1)=
      Sum.elim
        ((n:ℂ)⁻¹ • (ComplexifiedSkewBound.complexify S).mulVec (fun _ => 1))
        (-((n:ℂ)⁻¹ • (ComplexifiedSkewBound.complexify S).mulVec (fun _ => 1))) := by
  have htop : (ComplexifiedSkewBound.complexify S+(v:ℂ) • projection n).mulVec
      (fun _ => 1)=(ComplexifiedSkewBound.complexify S).mulVec (fun _ => 1) := by
    rw [Matrix.add_mulVec,Matrix.smul_mulVec,projection_ones hn,smul_zero,add_zero]
  have hbot : (-ComplexifiedSkewBound.complexify S+(v:ℂ) • projection n).mulVec
      (fun _ => 1)=-(ComplexifiedSkewBound.complexify S).mulVec (fun _ => 1) := by
    rw [Matrix.add_mulVec,Matrix.smul_mulVec,projection_ones hn,smul_zero,add_zero,
      Matrix.neg_mulVec]
  simp only [projectedInteraction,ProjectedTwoColorWoodbury.projectedInteraction,
    Matrix.smul_mulVec,Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def,Matrix.zero_mulVec,zero_add,add_zero,htop,hbot]
  ext i
  cases i <;> simp

end ProjectedTournamentDisk
#print axioms ProjectedTournamentDisk.projectedInteraction_bound
#print axioms ProjectedTournamentDisk.raw_inverse_disk
#print axioms ProjectedTournamentDisk.projected_inverse_disk
#print axioms ProjectedTournamentDisk.finite_interface_disk
#print axioms ProjectedTournamentDisk.parameter_disk
#print axioms ProjectedTournamentDisk.actual_parameter_disk
#print axioms ProjectedTournamentDisk.projected_scores
