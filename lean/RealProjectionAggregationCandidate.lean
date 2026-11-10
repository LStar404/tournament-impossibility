import RealGramEndpoint
import Mathlib.LinearAlgebra.Matrix.SchurComplement
set_option autoImplicit false
noncomputable section
namespace RealProjectionAggregationCandidate
open Matrix Finset RealGramEndpoint
open scoped Matrix.Norms.L2Operator
variable {r c : ℕ}
def g (Z : Matrix (Fin r) (Fin c) ℝ) : ℝ := -Real.log (1-Zᵀ*Z).det/2
lemma g_transpose (Z : Matrix (Fin r) (Fin c) ℝ) : g Zᵀ=g Z := by
  simp only [g,Matrix.transpose_transpose]
  rw [Matrix.det_one_sub_mul_comm Z Zᵀ]
lemma trace_gram (Z : Matrix (Fin r) (Fin c) ℝ) : (Zᵀ*Z).trace=frob Z := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.transpose_apply,frob,←pow_two]
  exact Finset.sum_comm
lemma projected_gram (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : Pᵀ=P) (hPP : P*P=P) : (P*Z)ᵀ*(P*Z)=Zᵀ*P*Z := by
  rw [Matrix.transpose_mul,hP]
  calc
    _ = Zᵀ*(P*P)*Z := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hPP]
lemma frob_loss (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : Pᵀ=P) (hPP : P*P=P) : frob ((1-P)*Z)=frob Z-frob (P*Z) := by
  rw [←trace_gram,←loss_gram Z P hP hPP]
  have he : loss Z P=Zᵀ*Z-(P*Z)ᵀ*(P*Z) := by
    rw [projected_gram Z P hP hPP]
    simp only [loss,Matrix.mul_sub,Matrix.mul_one,Matrix.sub_mul]
  rw [he,Matrix.trace_sub,trace_gram,trace_gram]
lemma projection_frob_contraction (Z : Matrix (Fin r) (Fin c) ℝ)
    (P : Matrix (Fin r) (Fin r) ℝ) (hP : Pᵀ=P) (hPP : P*P=P) :
    frob (P*Z)≤frob Z := by
  have hh := frob_loss Z P hP hPP
  have hn : 0≤frob ((1-P)*Z) := by unfold frob; positivity
  linarith
lemma frob_transpose (Z : Matrix (Fin r) (Fin c) ℝ) : frob Zᵀ=frob Z := by
  exact Finset.sum_comm
lemma projection_operator_contraction (Z : Matrix (Fin r) (Fin c) ℝ)
    (P : Matrix (Fin r) (Fin r) ℝ) (hP : Pᵀ=P) (hPP : P*P=P) :
    ‖P*Z‖≤‖Z‖ := by
  exact (Matrix.l2_opNorm_mul P Z).trans ((mul_le_mul_of_nonneg_right
    (projection_norm P hP hPP) (norm_nonneg Z)).trans_eq (one_mul _))
lemma left_g_loss (Z : Matrix (Fin r) (Fin c) ℝ) (P : Matrix (Fin r) (Fin r) ℝ)
    (hP : Pᵀ=P) (hPP : P*P=P) (q : ℝ) (hq : 0≤q) (hq1 : q<1) (hZ : ‖Z‖≤q) :
    ‖g (P*Z)-g Z‖≤frob ((1-P)*Z)/(2*(1-q^2)) := by
  have hh := logdet_endpoint Z P hP hPP q hq hq1 hZ
  have he : g (P*Z)-g Z= -(Real.log (1-Zᵀ*P*Z).det-Real.log (1-Zᵀ*Z).det)/2 := by
    simp only [g,projected_gram Z P hP hPP]
    ring
  rw [he,norm_div,norm_neg,show ‖(2:ℝ)‖=2 by norm_num]
  calc
    _ ≤ (frob ((1-P)*Z)/(1-q^2))/2 := div_le_div_of_nonneg_right hh (by norm_num)
    _ = _ := by rw [div_div]; congr 1; ring
lemma right_g_loss (Z : Matrix (Fin r) (Fin c) ℝ) (Q : Matrix (Fin c) (Fin c) ℝ)
    (hQ : Qᵀ=Q) (hQQ : Q*Q=Q) (q : ℝ) (hq : 0≤q) (hq1 : q<1) (hZ : ‖Z‖≤q) :
    ‖g (Z*Q)-g Z‖≤frob (Z*(1-Q))/(2*(1-q^2)) := by
  have hn : ‖Zᵀ‖≤q := by simpa only [←Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.l2_opNorm_conjTranspose] using hZ
  have hh := left_g_loss Zᵀ Q hQ hQQ q hq hq1 hn
  have he : Q*Zᵀ=(Z*Q)ᵀ := by rw [Matrix.transpose_mul,hQ]
  have hf : (1-Q)*Zᵀ=(Z*(1-Q))ᵀ := by simp only [Matrix.transpose_mul,Matrix.transpose_sub,Matrix.transpose_one,hQ]
  simpa only [he,hf,g_transpose,frob_transpose] using hh
lemma two_sided_g_loss (Z : Matrix (Fin r) (Fin c) ℝ)
    (P : Matrix (Fin r) (Fin r) ℝ) (Q : Matrix (Fin c) (Fin c) ℝ)
    (hP : Pᵀ=P) (hPP : P*P=P) (hQ : Qᵀ=Q) (hQQ : Q*Q=Q)
    (q : ℝ) (hq : 0≤q) (hq1 : q<1) (hZ : ‖Z‖≤q) :
    ‖g (P*Z*Q)-g Z‖ ≤ (frob ((1-P)*Z)+frob (Z*(1-Q)))/(2*(1-q^2)) := by
  have hl := left_g_loss Z P hP hPP q hq hq1 hZ
  have hr := right_g_loss (P*Z) Q hQ hQQ q hq hq1
    ((projection_operator_contraction Z P hP hPP).trans hZ)
  have hf : frob ((P*Z)*(1-Q))≤frob (Z*(1-Q)) := by
    rw [Matrix.mul_assoc]
    exact projection_frob_contraction _ P hP hPP
  have hd : 0≤2*(1-q^2) := by nlinarith
  calc
    _ ≤ ‖g (P*Z*Q)-g (P*Z)‖+‖g (P*Z)-g Z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ frob ((P*Z)*(1-Q))/(2*(1-q^2))+frob ((1-P)*Z)/(2*(1-q^2)) := add_le_add hr hl
    _ ≤ frob (Z*(1-Q))/(2*(1-q^2))+frob ((1-P)*Z)/(2*(1-q^2)) :=
      add_le_add (div_le_div_of_nonneg_right hf hd) le_rfl
    _ = _ := by ring
end RealProjectionAggregationCandidate

#print axioms RealProjectionAggregationCandidate.g
#check RealProjectionAggregationCandidate.g

#print axioms RealProjectionAggregationCandidate.g_transpose
#check RealProjectionAggregationCandidate.g_transpose

#print axioms RealProjectionAggregationCandidate.trace_gram
#check RealProjectionAggregationCandidate.trace_gram

#print axioms RealProjectionAggregationCandidate.projected_gram
#check RealProjectionAggregationCandidate.projected_gram

#print axioms RealProjectionAggregationCandidate.frob_loss
#check RealProjectionAggregationCandidate.frob_loss

#print axioms RealProjectionAggregationCandidate.projection_frob_contraction
#check RealProjectionAggregationCandidate.projection_frob_contraction

#print axioms RealProjectionAggregationCandidate.frob_transpose
#check RealProjectionAggregationCandidate.frob_transpose

#print axioms RealProjectionAggregationCandidate.projection_operator_contraction
#check RealProjectionAggregationCandidate.projection_operator_contraction

#print axioms RealProjectionAggregationCandidate.left_g_loss
#check RealProjectionAggregationCandidate.left_g_loss

#print axioms RealProjectionAggregationCandidate.right_g_loss
#check RealProjectionAggregationCandidate.right_g_loss

#print axioms RealProjectionAggregationCandidate.two_sided_g_loss
#check RealProjectionAggregationCandidate.two_sided_g_loss
