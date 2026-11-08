import DiamondFreeDiskResolvent

noncomputable section
open Matrix DiamondGap DiamondFreeKernelDeterminant DiamondFreeComplexResolvent
open DiamondFreeDiskResolvent WithLp
open scoped InnerProductSpace
namespace ActualComplexScoreSource

def integerScore {n : ℕ} (T : Tournament (Fin n)) (i : Fin n) : ℤ := ∑ j, T.S i j

def realScore {n : ℕ} (T : Tournament (Fin n)) (i : Fin n) : ℝ := integerScore T i

def complexScore {n : ℕ} (T : Tournament (Fin n)) (i : Fin n) : ℂ := integerScore T i

def scoreEnergy {n : ℕ} (T : Tournament (Fin n)) : ℝ := ∑ i, (realScore T i)^2

lemma complexScore_eq_mulVec {n : ℕ} (T : Tournament (Fin n)) :
    complexScore T = (signMatrix T : Matrix (Fin n) (Fin n) ℂ).mulVec (fun _ => 1) := by
  ext i
  simp [complexScore, integerScore, Matrix.mulVec, dotProduct, signMatrix]

lemma ofLp_score {n : ℕ} (T : Tournament (Fin n)) :
    ofLp (scoreVector T) = complexScore T := by
  rw [complexScore_eq_mulVec]
  rfl

lemma complexScore_real {n : ℕ} (T : Tournament (Fin n)) (i : Fin n) :
    complexScore T i = (realScore T i : ℂ) := by
  simp [complexScore, realScore]

lemma star_score {n : ℕ} (T : Tournament (Fin n)) : star (complexScore T) = complexScore T := by
  ext i
  simp [complexScore_real]

lemma norm_score_sq {n : ℕ} (T : Tournament (Fin n)) :
    ‖scoreVector T‖^2=scoreEnergy T := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold scoreEnergy
  apply Finset.sum_congr rfl
  intro i hi
  have he : scoreVector T i = (realScore T i : ℂ) := by
    exact congrFun (ofLp_score T) i |>.trans (complexScore_real T i)
  rw [he]
  simp

/-- The source is the ordinary bilinear matrix expression b^T M b, since the
actual score vector has real coordinates, even though M may be complex. -/
theorem inner_eq_bilinear {n : ℕ} (T : Tournament (Fin n))
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ⟪scoreVector T, (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M) (scoreVector T)⟫_ℂ =
      complexScore T ⬝ᵥ (M.mulVec (complexScore T)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM,
    ofLp_score, star_score, dotProduct_comm]

def source {n : ℕ} (T : Tournament (Fin n)) (w : ℂ) : ℂ :=
  complexScore T ⬝ᵥ ((resolventMatrix T w)⁻¹).mulVec (complexScore T)

/-- A radius-only threshold controls the ordinary S1 bilinear source, uniformly
in the zero-diamond graph, disk parameter, and energy constant. -/
theorem eventually_uniform_actual_source {r : ℝ} (hr : 0≤r) (hrpi : r<Real.pi/2) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (T : Tournament (Fin n)), T.diamonds.card=0 →
      ∀ w : ℂ, ‖w‖≤r → ∀ K : ℝ, scoreEnergy T≤K*(n:ℝ) →
        ‖source T w‖/(n:ℝ)^2 ≤ K*(diskConstant r)^2/(n:ℝ) := by
  filter_upwards [eventually_uniform_source hr hrpi] with n hn
  intro T hT w hw K henergy
  have h := hn T hT w hw (scoreVector T) K (by simpa [norm_score_sq] using henergy)
  simpa only [inner_eq_bilinear, source] using h

end ActualComplexScoreSource
#print axioms ActualComplexScoreSource.inner_eq_bilinear
#print axioms ActualComplexScoreSource.norm_score_sq
#print axioms ActualComplexScoreSource.eventually_uniform_actual_source
