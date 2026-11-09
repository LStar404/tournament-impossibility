import ComplexifiedSkewBound
import RawBlockNeumannInverse
noncomputable section
namespace TournamentSkewMargin
open Matrix
open scoped Matrix.Norms.L2Operator

theorem unnormalized {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (ComplexifiedSkewBound.complexify S)‖ ≤ (n:ℝ)*(17/24) := by
  apply ComplexifiedSkewBound.operator_bound S hS _ (by positivity)
  have hh : (∑ i,∑ j,S i j^2) ≤ (n:ℝ)^2 := by
    calc
      _ ≤ ∑ i:Fin n, ∑ j:Fin n,(1:ℝ) := Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => by have h := he i j; exact (sq_le_one_iff_abs_le_one _).mpr h))
      _ = _ := by simp; ring
  nlinarith [sq_nonneg (n:ℝ)]

def branch {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (n:ℂ)⁻¹ • (ComplexifiedSkewBound.complexify S+(v:ℂ) • (1:Matrix (Fin n) (Fin n) ℂ))

theorem branch_bound {n : ℕ} (hn : 24 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (v : ℝ) (hv : |v| ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (branch S v)‖ ≤ 3/4 := by
  have hnR : (24:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hu := unnormalized S hS he
  have hi : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (1:Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [map_one]; exact ContinuousLinearMap.norm_id_le
  have hs : ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
      (ComplexifiedSkewBound.complexify S+(v:ℂ) • (1:Matrix (Fin n) (Fin n) ℂ))‖ ≤ (n:ℝ)*(17/24)+1 := by
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
end TournamentSkewMargin
#print axioms TournamentSkewMargin.branch_bound
