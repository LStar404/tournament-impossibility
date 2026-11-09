import PermanentCircleRankOne
import Mathlib.Analysis.InnerProductSpace.Adjoint
noncomputable section
namespace PermanentSpectralFrame
open Matrix
variable {n : ℕ}
def averaging (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun _ _ => (n:ℂ)⁻¹
def centered (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1-averaging n)*M*(1-averaging n)
lemma averaging_square (hn : 0<n) : averaging n*averaging n=averaging n := by
  ext i j
  simp only [averaging,Matrix.mul_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hnC : (n:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
lemma averaging_adjoint (n : ℕ) : (averaging n)ᴴ=averaging n := by
  ext i j
  simp [averaging, Matrix.conjTranspose_apply]
lemma averaging_rankOne (n : ℕ) : averaging n=rankOne (fun _ => (1:ℂ)) (fun _ => (n:ℂ)⁻¹) := by
  ext i j
  simp [averaging,rankOne]
lemma centered_left_zero (hn : 0<n) (M : Matrix (Fin n) (Fin n) ℂ) :
    averaging n * centered M=0 := by
  unfold centered
  have hh : averaging n*(1-averaging n)=0 := by rw [mul_sub,mul_one,averaging_square hn,sub_self]
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hh,zero_mul,zero_mul]
lemma centered_right_zero (hn : 0<n) (M : Matrix (Fin n) (Fin n) ℂ) :
    centered M * averaging n=0 := by
  unfold centered
  have hh : (1-averaging n)*averaging n=0 := by rw [sub_mul,one_mul,averaging_square hn,sub_self]
  rw [Matrix.mul_assoc,Matrix.mul_assoc,hh,mul_zero,mul_zero]
lemma centering_residual (M : Matrix (Fin n) (Fin n) ℂ) :
    M-centered M=averaging n*M+(1-averaging n)*M*averaging n := by
  unfold centered
  noncomm_ring

/-- The sharp top bound uses a genuine orthogonal splitting, not norm(P)+norm(E). -/
lemma orthogonal_block_contraction {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (P N : H →L[ℂ] H) (hP : P.adjoint=P) (hPP : P*P=P)
    (hPN : P*N=0) (hNP : N*P=0) (hN : ‖N‖≤1) : ‖P+N‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hPPx : P (P x)=P x := DFunLike.congr_fun hPP x
  have hPNx : P (N x)=0 := DFunLike.congr_fun hPN x
  have hNPx : N (P x)=0 := DFunLike.congr_fun hNP x
  have hi : inner ℂ (P x) (x-P x)=0 := by
    calc
      inner ℂ (P x) (x-P x) = inner ℂ (P.adjoint x) (x-P x) := by rw [hP]
      _ = inner ℂ x (P (x-P x)) := ContinuousLinearMap.adjoint_inner_left P _ _
      _ = 0 := by rw [map_sub,hPPx,sub_self,inner_zero_right]
  have hj : inner ℂ (P x) (N x)=0 := by
    calc
      inner ℂ (P x) (N x) = inner ℂ (P.adjoint x) (N x) := by rw [hP]
      _ = inner ℂ x (P (N x)) := ContinuousLinearMap.adjoint_inner_left P _ _
      _ = 0 := by rw [hPNx,inner_zero_right]
  have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (x-P x) hi
  have ht := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (N x) hj
  have hn := (N.le_opNorm (x-P x)).trans
    (mul_le_mul_of_nonneg_right hN (norm_nonneg _))
  simp only [map_sub,hNPx,sub_zero,one_mul] at hn
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hx : P x+(x-P x)=x := by abel
  rw [hx] at hs
  change ‖P x+N x‖≤1*‖x‖
  rw [one_mul]
  nlinarith [norm_nonneg (P x+N x),norm_nonneg x]
end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.orthogonal_block_contraction
