import RawFourBlockResolvent
import PermanentCircleCentering
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
Independent finite-algebra extension; not part of the frozen 372 source tree.

Replace b*I by b*Pi in both off-diagonal blocks, with Pi = I-J/n.
The update is factored through Bool (two colors). Woodbury uses C = I, so
b = 0 and the origin are allowed. No canonical-numbering input is used.
-/
noncomputable section
namespace ProjectedTwoColorWoodbury
open Matrix RawFourBlockResolvent
variable {n : ℕ}

def projection (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  1-PermanentSpectralFrame.averaging n

lemma projection_transpose (n : ℕ) : (projection n).transpose=projection n := by
  have hP : (PermanentSpectralFrame.averaging n).transpose=
      PermanentSpectralFrame.averaging n := by
    ext i j
    rfl
  rw [projection,Matrix.transpose_sub,Matrix.transpose_one,hP]

lemma projection_square (hn : 0<n) : projection n*projection n=projection n := by
  unfold projection
  calc
    _ = 1-PermanentSpectralFrame.averaging n-PermanentSpectralFrame.averaging n+
        PermanentSpectralFrame.averaging n*PermanentSpectralFrame.averaging n := by
      noncomm_ring
    _ = _ := by rw [PermanentSpectralFrame.averaging_square hn]; abel

lemma projection_ones (hn : 0<n) :
    (projection n).mulVec (fun _ => 1)=0 := by
  have hnC : (n:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hP : (PermanentSpectralFrame.averaging n).mulVec (fun _ => 1)=
      (fun _ : Fin n => (1:ℂ)) := by
    ext i
    simp [PermanentSpectralFrame.averaging,Matrix.mulVec,dotProduct,nsmul_eq_mul,hnC]
  rw [projection,Matrix.sub_mulVec,Matrix.one_mulVec,hP,sub_self]

def projectedSystem (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fromBlocks 1 (f • C+b • projection n) (-(f • C)+b • projection n) 1

lemma projectedSystem_transpose_blocks (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ)
    (hC : C.transpose=-C) :
    projectedSystem C f b=fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ)
      (f • C+b • projection n) (f • C+b • projection n).transpose 1 := by
  simp only [projectedSystem,Matrix.transpose_add,Matrix.transpose_smul,
    hC,projection_transpose,smul_neg]

def columns (n : ℕ) : Matrix (Fin n ⊕ Fin n) Bool ℂ :=
  fun i c => Sum.elim (fun _ => if c then 0 else 1) (fun _ => if c then 1 else 0) i

def rows (n : ℕ) (b : ℂ) : Matrix Bool (Fin n ⊕ Fin n) ℂ :=
  fun c j => Sum.elim (fun _ => if c then -b*(n:ℂ)⁻¹ else 0)
    (fun _ => if c then 0 else -b*(n:ℂ)⁻¹) j

lemma update_four_blocks (b : ℂ) :
    columns n*rows n b = fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ)
      (-(b • PermanentSpectralFrame.averaging n))
      (-(b • PermanentSpectralFrame.averaging n)) 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [columns,rows,Matrix.mul_apply,Matrix.fromBlocks,
      PermanentSpectralFrame.averaging]

/-- Exact update, including the sign of both off-diagonal perturbations. -/
theorem projected_eq_update (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ) :
    projectedSystem C f b=system C f b+columns n*rows n b := by
  rw [update_four_blocks]
  unfold projectedSystem system upper lower projection
  rw [Matrix.fromBlocks_add]
  congr 1 <;> module

def innerMatrix (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ) : Matrix Bool Bool ℂ :=
  1+rows n b*(system C f b)⁻¹*columns n

def correction (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (system C f b)⁻¹*columns n*(innerMatrix C f b)⁻¹*rows n b*(system C f b)⁻¹

/-- Generic finite-dimensional invertibility transport used alongside the
library's nonsingular-inverse Woodbury theorem. -/
lemma isUnit_add_mul {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (U : Matrix I J ℂ) (V : Matrix J I ℂ)
    (hA : IsUnit A) (hsmall : IsUnit (1+V*A⁻¹*U)) : IsUnit (A+U*V) := by
  obtain ⟨iA⟩ := hA.nonempty_invertible
  let : Invertible A := iA
  let : Invertible (1 : Matrix J J ℂ) := invertibleOne
  have hs : IsUnit (⅟(1 : Matrix J J ℂ)+V*⅟A*U) := by
    simpa only [invOf_one,Matrix.invOf_eq_nonsing_inv] using hsmall
  obtain ⟨iSmall⟩ := hs.nonempty_invertible
  let : Invertible (⅟(1 : Matrix J J ℂ)+V*⅟A*U) := iSmall
  let := Matrix.invertibleAddMulMul A U (1 : Matrix J J ℂ) V
  simpa only [Matrix.mul_one] using
    (isUnit_of_invertible (A+U*(1 : Matrix J J ℂ)*V))

theorem isUnit_projected (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ)
    (hD : IsUnit (schur C f b)) (hsmall : IsUnit (innerMatrix C f b)) :
    IsUnit (projectedSystem C f b) := by
  rw [projected_eq_update]
  exact isUnit_add_mul _ _ _ (isUnit_system C f b hD) hsmall

/-- The actual projected inverse. Only the unprojected Schur matrix and the
explicit 2-by-2 inner matrix have invertibility hypotheses. -/
theorem inverse_woodbury (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ)
    (hD : IsUnit (schur C f b)) (hsmall : IsUnit (innerMatrix C f b)) :
    (projectedSystem C f b)⁻¹=(system C f b)⁻¹-correction C f b := by
  have hs : IsUnit ((1 : Matrix Bool Bool ℂ)⁻¹+
      rows n b*(system C f b)⁻¹*columns n) := by
    simpa only [inv_one,innerMatrix] using hsmall
  have h := Matrix.add_mul_mul_inv_eq_sub (system C f b) (columns n)
    (1 : Matrix Bool Bool ℂ) (rows n b) (isUnit_system C f b hD) isUnit_one hs
  rw [projected_eq_update]
  simpa only [Matrix.mul_one,inv_one,correction,innerMatrix] using h

/-- Substituting the proven four-block inverse makes the 2-by-2 denominator
depend only on the single unprojected Schur resolvent. -/
theorem innerMatrix_four_blocks (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ)
    (hD : IsUnit (schur C f b)) :
    innerMatrix C f b=1+rows n b*
      fromBlocks (resolvent C f b) (-(upper C f b*resolvent C f b))
        (-(lower C f b*resolvent C f b)) (resolvent C f b)*columns n := by
  unfold innerMatrix
  rw [inverse_four_blocks C f b hD]

def projectedKernel (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  (projectedSystem C f b-1)*(projectedSystem C f b)⁻¹

theorem kernel_difference (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ)
    (hD : IsUnit (schur C f b)) (hsmall : IsUnit (innerMatrix C f b)) :
    projectedKernel C f b-kernel C f b=correction C f b := by
  unfold projectedKernel kernel
  rw [difference_times_inverse _ (isUnit_projected C f b hD hsmall),
    difference_times_inverse _ (isUnit_system C f b hD),inverse_woodbury C f b hD hsmall]
  abel

theorem mean_difference (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ)
    (hD : IsUnit (schur C f b)) (hsmall : IsUnit (innerMatrix C f b)) :
    (projectedKernel C f b).mulVec (fun _ => 1)-
      (kernel C f b).mulVec (fun _ => 1)=
        (correction C f b).mulVec (fun _ => 1) := by
  rw [← Matrix.sub_mulVec,kernel_difference C f b hD hsmall]

/-- Reuses the existing actual rawSource, including its factor 1/2. -/
theorem source_difference (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ)
    (hD : IsUnit (schur C f b)) (hsmall : IsUnit (innerMatrix C f b)) :
    RawBlockSourceIdentity.rawSource (projectedSystem C f b)-
      RawBlockSourceIdentity.rawSource (system C f b)=
        (RawBlockSourceIdentity.ones n ⬝ᵥ
          (correction C f b).mulVec (RawBlockSourceIdentity.ones n))/2 := by
  have h := congrArg (fun W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ =>
    (RawBlockSourceIdentity.ones n ⬝ᵥ W.mulVec (RawBlockSourceIdentity.ones n))/2)
      (kernel_difference C f b hD hsmall)
  simpa only [Matrix.sub_mulVec,dotProduct_sub,sub_div,
    projectedKernel,kernel,RawBlockSourceIdentity.rawSource] using h

def sector (c : Bool) (i : Fin n) : Fin n ⊕ Fin n := if c then Sum.inr i else Sum.inl i

/-- Sum over one actual block; the order is column then row, to match V*R*U. -/
def blockMass (R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (c d : Bool) : ℂ :=
  ∑j,∑i,R (sector c i) (sector d j)

lemma contraction_apply (R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (b : ℂ) (c d : Bool) :
    (rows n b*R*columns n) c d=(-b*(n:ℂ)⁻¹)*blockMass R (!c) d := by
  cases c <;> cases d <;>
    simp [rows,columns,blockMass,sector,Matrix.mul_apply,Fintype.sum_sum_type,
      Finset.mul_sum,Finset.sum_mul]

/-- Fully explicit entries of the two-color denominator. No implicit rank
factorization or inverse-at-zero assumption is left in this definition. -/
theorem innerMatrix_apply (C : Matrix (Fin n) (Fin n) ℂ) (f b : ℂ) (c d : Bool) :
    innerMatrix C f b c d=(if c=d then 1 else 0)+
      (-b*(n:ℂ)⁻¹)*blockMass ((system C f b)⁻¹) (!c) d := by
  change (1 : Matrix Bool Bool ℂ) c d+
    (rows n b*(system C f b)⁻¹*columns n) c d= _
  rw [Matrix.one_apply,contraction_apply]

lemma rows_zero (n : ℕ) : rows n 0=0 := by
  ext c i
  cases c <;> cases i <;> simp [rows]

theorem zero_parameter (C : Matrix (Fin n) (Fin n) ℂ) (f : ℂ) :
    projectedSystem C f 0=system C f 0 ∧
      innerMatrix C f 0=1 ∧ correction C f 0=0 := by
  constructor
  · rw [projected_eq_update,rows_zero,Matrix.mul_zero,add_zero]
  constructor
  · simp [innerMatrix,rows_zero]
  · simp [correction,rows_zero]

def projectedInteraction (C : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  fromBlocks 0 (C+v • projection n) (-C+v • projection n) 0

theorem actual_eq_projectedSystem (C : Matrix (Fin n) (Fin n) ℂ) (a v : ℂ) :
    AffineMatrixTaylorBridge.actual (projectedInteraction C v) a=
      projectedSystem C a (a*v) := by
  unfold AffineMatrixTaylorBridge.actual projectedInteraction projectedSystem
  rw [Matrix.fromBlocks_smul,← Matrix.fromBlocks_one,Matrix.fromBlocks_add]
  simp [smul_add,smul_neg,smul_smul]

theorem raw_covariance_eq_projectedKernel (C : Matrix (Fin n) (Fin n) ℂ) (a v : ℂ) :
    RawCoordinateTaylor.covariance (projectedInteraction C v) a=
      projectedKernel C a (a*v) := by
  have hdiff : a • projectedInteraction C v=projectedSystem C a (a*v)-1 := by
    rw [← actual_eq_projectedSystem]
    simp only [AffineMatrixTaylorBridge.actual,add_sub_cancel_left]
  unfold RawCoordinateTaylor.covariance projectedKernel
  -- Match the equality instance fixed by the existing covariance definition.
  have hdec : Classical.typeDecidableEq (Fin n ⊕ Fin n) =
      (inferInstance : DecidableEq (Fin n ⊕ Fin n)) := Subsingleton.elim _ _
  rw [hdec,actual_eq_projectedSystem,hdiff]

/-- The Woodbury correction compares the existing physical analytic
covariances, not newly defined unrelated kernels. -/
theorem actual_covariance_difference (C : Matrix (Fin n) (Fin n) ℂ) (a v : ℂ)
    (hD : IsUnit (schur C a (a*v))) (hsmall : IsUnit (innerMatrix C a (a*v))) :
    RawCoordinateTaylor.covariance (projectedInteraction C v) a-
      RawCoordinateTaylor.covariance (interaction C v) a=correction C a (a*v) := by
  rw [raw_covariance_eq_projectedKernel,raw_covariance_eq_kernel]
  exact kernel_difference C a (a*v) hD hsmall

end ProjectedTwoColorWoodbury
#print axioms ProjectedTwoColorWoodbury.inverse_woodbury
#print axioms ProjectedTwoColorWoodbury.innerMatrix_apply
#print axioms ProjectedTwoColorWoodbury.source_difference
#print axioms ProjectedTwoColorWoodbury.actual_covariance_difference
