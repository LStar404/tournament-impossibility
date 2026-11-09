import RawBlockInverseScaling

noncomputable section
namespace RawBlockNeumannInverse
open Matrix
open scoped Matrix.Norms.L2Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem inverse_bound (Q : Matrix I I ℂ) (z : ℂ) {s q : ℝ}
    (hs : ‖z‖ ≤ s) (hq : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) Q‖ ≤ q)
    (hgap : s*q < 1) :
    IsUnit ((1 : Matrix I I ℂ)+z • Q) ∧
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (((1 : Matrix I I ℂ)+z • Q)⁻¹)‖ ≤ 1/(1-s*q) := by
  have hs0 : 0 ≤ s := (norm_nonneg z).trans hs
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hq
  have hn : ‖-(z • Q)‖ ≤ s*q := by
    rw [norm_neg,norm_smul]
    exact mul_le_mul hs hq (norm_nonneg _) hs0
  have hsmall : ‖-(z • Q)‖ < 1 := hn.trans_lt hgap
  have hu : IsUnit ((1 : Matrix I I ℂ)+z • Q) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hsmall
  refine ⟨hu,?_⟩
  have hgeom := tsum_geometric_le_of_norm_lt_one (-(z • Q)) hsmall
  rw [geom_series_eq_inverse _ hsmall,sub_neg_eq_add,← Matrix.nonsing_inv_eq_ringInverse] at hgeom
  have h1 : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM,map_one]
    exact ContinuousLinearMap.norm_id_le
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  calc
    _ ≤ ‖(1 : Matrix I I ℂ)‖-1+(1-‖-(z • Q)‖)⁻¹ := hgeom
    _ ≤ 1/(1-s*q) := by
      have hpos : 0 < 1-s*q := by linarith
      have hinv : (1-‖-(z • Q)‖)⁻¹ ≤ (1-s*q)⁻¹ :=
        inv_anti₀ hpos (by linarith)
      rw [one_div]
      linarith
end RawBlockNeumannInverse
#print axioms RawBlockNeumannInverse.inverse_bound
