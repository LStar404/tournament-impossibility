import TournamentSkewMargin
noncomputable section
namespace BipartiteOperatorBound
open Matrix WithLp
variable {I : Type*} [Fintype I] [DecidableEq I]
def block (M N : Matrix I I ℂ) : Matrix (I ⊕ I) (I ⊕ I) ℂ :=
  Matrix.fromBlocks 0 M N 0

theorem bound (M N : Matrix I I ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hM : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) M‖ ≤ q)
    (hN : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) N‖ ≤ q) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (block M N)‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro x
  let a : I → ℂ := fun i => (ofLp x) (Sum.inl i)
  let b : I → ℂ := fun i => (ofLp x) (Sum.inr i)
  have hm : ‖toLp 2 (M.mulVec b)‖ ≤ q*‖toLp 2 b‖ := by
    have h := (Matrix.toEuclideanCLM (𝕜:=ℂ) M).le_opNorm (toLp 2 b)
    exact h.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  have hn : ‖toLp 2 (N.mulVec a)‖ ≤ q*‖toLp 2 a‖ := by
    have h := (Matrix.toEuclideanCLM (𝕜:=ℂ) N).le_opNorm (toLp 2 a)
    exact h.trans (mul_le_mul_of_nonneg_right hN (norm_nonneg _))
  have hs : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (block M N) x‖^2 =
      ‖toLp 2 (M.mulVec b)‖^2+‖toLp 2 (N.mulVec a)‖^2 := by
    simp [EuclideanSpace.norm_sq_eq,Matrix.ofLp_toEuclideanCLM,
      block,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,a,b]
  have hx : ‖x‖^2=‖toLp 2 a‖^2+‖toLp 2 b‖^2 := by
    simp [EuclideanSpace.norm_sq_eq,Fintype.sum_sum_type,a,b]
  have hm2 := sq_le_sq₀ (norm_nonneg (toLp 2 (M.mulVec b)))
    (mul_nonneg hq (norm_nonneg (toLp 2 b))) |>.mpr hm
  have hn2 := sq_le_sq₀ (norm_nonneg (toLp 2 (N.mulVec a)))
    (mul_nonneg hq (norm_nonneg (toLp 2 a))) |>.mpr hn
  have hnon := mul_nonneg hq (norm_nonneg x)
  apply (sq_le_sq₀ (norm_nonneg _) hnon).mp
  calc
    _ = _ := hs
    _ ≤ (q*‖toLp 2 b‖)^2+(q*‖toLp 2 a‖)^2 := add_le_add hm2 hn2
    _ = (q*‖x‖)^2 := by simp only [mul_pow,hx]; ring
theorem tournament_bound {n : ℕ} (hn : 24 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (v : ℝ) (hv : |v| ≤ 1) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (block (TournamentSkewMargin.branch S v)
      (TournamentSkewMargin.branch S v).transpose)‖ ≤ 3/4 := by
  apply bound _ _ _ (by norm_num) (TournamentSkewMargin.branch_bound hn S hS he v hv)
  have ht : (TournamentSkewMargin.branch S v).transpose=
      TournamentSkewMargin.branch S.transpose v := by
    ext i j
    simp [TournamentSkewMargin.branch,ComplexifiedSkewBound.complexify,
      Matrix.transpose_apply,Matrix.one_apply,eq_comm]
    split_ifs <;> ring
  rw [ht]
  exact TournamentSkewMargin.branch_bound hn S.transpose
    (fun i j => hS j i) (fun i j => he j i) v hv

end BipartiteOperatorBound
#print axioms BipartiteOperatorBound.bound
