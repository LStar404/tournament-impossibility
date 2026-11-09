import RawBlockInverseScaling

noncomputable section
namespace BalancedTensorScores
open Matrix
variable {C F : Type*} [Fintype C] [Fintype F] [DecidableEq C]

def matrix (A : Matrix F F ℂ) (B : Matrix C C ℂ) (t : F → ℂ) : Matrix (C × F) (C × F) ℂ :=
  fun x y => (if x.1=y.1 then A x.2 y.2 else 0)+B x.1 y.1*t x.2*t y.2

theorem score (A : Matrix F F ℂ) (B : Matrix C C ℂ) (t : F → ℂ)
    (ht : ∑a,t a=0) (x : C × F) :
    ((matrix A B t).mulVec (fun _ => 1)) x=∑b,A x.2 b := by
  simp only [matrix,Matrix.mulVec,dotProduct,mul_one,Fintype.sum_prod_type,
    Finset.sum_add_distrib]
  simp only [← Finset.mul_sum,ht,mul_zero,add_zero]
  simp

/-- Fixed finite block gives bounded actual scores, independently of the coarse matrix. -/
theorem score_bound (A : Matrix F F ℂ) (B : Matrix C C ℂ) (t : F → ℂ)
    (ht : ∑a,t a=0) {L : ℝ} (hA : ∀a b,‖A a b‖ ≤ L) (x : C × F) :
    ‖((matrix A B t).mulVec (fun _ => 1)) x‖ ≤ (Fintype.card F:ℝ)*L := by
  rw [score A B t ht]
  exact (norm_sum_le _ _).trans (by
    calc
      _ ≤ ∑b:F,L := Finset.sum_le_sum (fun b hb => hA x.2 b)
      _ = _ := by simp)
theorem branch_score [DecidableEq F] (A : Matrix F F ℂ) (B : Matrix C C ℂ) (t : F → ℂ)
    (ht : ∑a,t a=0) (v : ℂ) (n : ℕ) (hn : 0<n) {L : ℝ} (hA : ∀a b,‖A a b‖ ≤ L)
    (x : C × F) :
    ‖((((n:ℂ)⁻¹ • (matrix A B t+v • (1 : Matrix (C × F) (C × F) ℂ))).mulVec
      (fun _ => 1)) x)‖ ≤ ((Fintype.card F:ℝ)*L+‖v‖)/(n:ℝ) := by
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.one_mulVec,Pi.smul_apply,
    Pi.add_apply,smul_eq_mul,mul_one,norm_mul,norm_inv,Complex.norm_natCast]
  have hh := (norm_add_le _ _).trans (add_le_add_right (score_bound A B t ht hA x) ‖v‖)
  simpa only [div_eq_mul_inv,mul_comm,add_comm] using
    mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Nat.cast_nonneg n))

theorem transpose_matrix (A : Matrix F F ℂ) (B : Matrix C C ℂ) (t : F → ℂ) :
    (matrix A B t).transpose=matrix A.transpose B.transpose t := by
  ext x y
  simp only [matrix,Matrix.transpose_apply]
  by_cases h : x.1=y.1 <;> simp only [h,eq_comm,ite_true,ite_false] <;> ring

theorem branch_column_score [DecidableEq F] (A : Matrix F F ℂ) (B : Matrix C C ℂ) (t : F → ℂ)
    (ht : ∑a,t a=0) (v : ℂ) (n : ℕ) (hn : 0<n) {L : ℝ} (hA : ∀a b,‖A a b‖ ≤ L)
    (x : C × F) :
    ‖((((n:ℂ)⁻¹ • (matrix A B t+v • (1 : Matrix (C × F) (C × F) ℂ))).transpose).mulVec
      (fun _ => 1) x)‖ ≤ ((Fintype.card F:ℝ)*L+‖v‖)/(n:ℝ) := by
  simpa only [Matrix.transpose_smul,Matrix.transpose_add,Matrix.transpose_one,transpose_matrix] using
    branch_score A.transpose B.transpose t ht v n hn (fun a b => hA b a) x

end BalancedTensorScores
#print axioms BalancedTensorScores.score_bound

#print axioms BalancedTensorScores.branch_score

#print axioms BalancedTensorScores.branch_column_score
