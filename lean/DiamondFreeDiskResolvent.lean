import DiamondFreeKernelOperatorBound
import ComplexKernelDiskLower
import DiamondFreeComplexResolvent

noncomputable section
open Matrix DiamondGap DiamondFreeKernelDeterminant DiamondFreeComplexResolvent
open scoped InnerProductSpace
namespace DiamondFreeDiskResolvent

/-- A non-sharp but dimension-independent explicit bound. -/
def diskConstant (R : ℝ) : ℝ := (1+R)*Real.exp R/(Real.cos R/2)

lemma H_neg (n : ℕ) (a : ℂ) :
    TransitiveKernelInverse.H n (-a)=TransitiveKernelInverse.H n a := by
  simp [TransitiveKernelInverse.H, sub_eq_add_neg, add_comm]

variable {n : ℕ} (hn : 0 < n) (T : Tournament (Fin n)) (hT : T.diamonds.card=0)
  {R : ℝ} (hR : 0 ≤ R) (hpi : R < Real.pi/2)
  (hsmall : R/(n : ℝ) ≤ 1/2) (herr : R^2/(n : ℝ) ≤ 1)
  (hthreshold : 2*Real.exp R*R^2/(n : ℝ) ≤ Real.cos R/2)
  {w : ℂ} (hw : ‖w‖ ≤ R)

include hn hR hpi hsmall herr hthreshold hw in
lemma denominator_lower :
    Real.cos R/2 ≤ ‖TransitiveKernelInverse.H n (w*Complex.I/(n : ℂ))‖ := by
  simpa [TransitiveKernelInverse.H, DiamondFreeKernelLimit.finiteKernel] using
    ComplexKernelDiskLower.finite_kernel_lower n hn hR hpi hsmall herr hthreshold hw

include hR hpi in
lemma cosine_positive : 0 < Real.cos R :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩

include hn hT hR hpi hsmall herr hthreshold hw in
/-- Uniform finite-order norm control of both genuine linear kernel inverses.
The order threshold discharges the determinant lower bound, and the operator
bound comes from explicit inverse entries, not from determinants alone. -/
theorem linear_inverse_bounds :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
      ((kernel T (w*Complex.I/(n : ℂ)))⁻¹)‖ ≤ diskConstant R ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
      ((kernel T (-(w*Complex.I/(n : ℂ))))⁻¹)‖ ≤ diskConstant R := by
  have hc : 0 < Real.cos R/2 := by
    have hcos := cosine_positive hR hpi
    positivity
  have ha : ‖w*Complex.I/(n : ℂ)‖ ≤ R/(n : ℝ) := by
    simpa using div_le_div_of_nonneg_right hw (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hH := denominator_lower hn hR hpi hsmall herr hthreshold hw
  constructor
  · exact DiamondFreeKernelOperatorBound.actual_operator_bound hn T hT _ R _ ha hc hH
  · exact DiamondFreeKernelOperatorBound.actual_operator_bound hn T hT _ R _
      (by simpa using ha) hc (by simpa only [H_neg] using hH)

include hn hT hR hpi hsmall herr hthreshold hw in
/-- The finite threshold gives a truly invertible quadratic resolvent matrix,
not merely the totalized inverse assigned by Lean to singular matrices. -/
theorem inverse_left_right :
    resolventMatrix T w * (resolventMatrix T w)⁻¹=1 ∧
      (resolventMatrix T w)⁻¹ * resolventMatrix T w=1 := by
  have hc : 0 < Real.cos R/2 := by
    have hcos := cosine_positive hR hpi
    positivity
  have hH := denominator_lower hn hR hpi hsmall herr hthreshold hw
  have hp : TransitiveKernelInverse.H n (w*Complex.I/(n : ℂ)) ≠ 0 :=
    norm_pos_iff.mp (hc.trans_le hH)
  have hm : TransitiveKernelInverse.H n (-(w*Complex.I/(n : ℂ))) ≠ 0 := by
    simpa only [H_neg] using hp
  have hd (a : ℂ) : (kernel T a).det=TransitiveKernelInverse.H n a := by
    simpa [TransitiveKernelInverse.H] using zero_diamonds_kernel_det T hT a
  have hdet : (resolventMatrix T w).det ≠ 0 := by
    rw [factorization, det_mul, hd, hd]
    exact mul_ne_zero hp hm
  exact ⟨Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)⟩

include hn hT hR hpi hsmall herr hthreshold hw in
/-- A dimension-uniform actual quadratic inverse operator bound on the entire
closed disk, with an explicit finite-order threshold. -/
theorem inverse_operator_bound :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) ((resolventMatrix T w)⁻¹)‖ ≤
      (diskConstant R)^2 := by
  obtain ⟨hp,hm⟩ := linear_inverse_bounds hn T hT hR hpi hsmall herr hthreshold hw
  have hc : 0 ≤ diskConstant R := by
    unfold diskConstant
    have hcos := cosine_positive hR hpi
    positivity
  rw [factorization, Matrix.mul_inv_rev, map_mul]
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
          ((kernel T (-(w*Complex.I/(n : ℂ))))⁻¹)‖ *
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
          ((kernel T (w*Complex.I/(n : ℂ)))⁻¹)‖ := norm_mul_le _ _
    _ ≤ diskConstant R * diskConstant R := mul_le_mul hm hp (norm_nonneg _) hc
    _ = _ := by ring

include hn hT hR hpi hsmall herr hthreshold hw in
/-- The complex Hilbert source form of the actual matrix inverse. -/
theorem source_bound (b : EuclideanSpace ℂ (Fin n)) :
    ‖⟪b, (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
      ((resolventMatrix T w)⁻¹)) b⟫_ℂ‖ ≤ ‖b‖^2*(diskConstant R)^2 := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) ((resolventMatrix T w)⁻¹)
  have hL : ‖L‖ ≤ (diskConstant R)^2 :=
    inverse_operator_bound hn T hT hR hpi hsmall herr hthreshold hw
  calc
    _ ≤ ‖b‖*‖L b‖ := norm_inner_le_norm _ _
    _ ≤ ‖b‖*(‖L‖*‖b‖) := mul_le_mul_of_nonneg_left (L.le_opNorm b) (norm_nonneg b)
    _ ≤ ‖b‖*((diskConstant R)^2*‖b‖) := by gcongr
    _ = _ := by ring

include hn hT hR hpi hsmall herr hthreshold hw in
/-- After actual linear source energy, the quadratic-normalized source has a
fully explicit O(1/n) bound. No spectral or operator-norm premise remains. -/
theorem normalized_source_bound (b : EuclideanSpace ℂ (Fin n)) {K : ℝ}
    (henergy : ‖b‖^2 ≤ K*(n : ℝ)) :
    ‖⟪b, (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
      ((resolventMatrix T w)⁻¹)) b⟫_ℂ‖/(n : ℝ)^2 ≤ K*(diskConstant R)^2/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (‖b‖^2*(diskConstant R)^2)/(n : ℝ)^2 :=
      div_le_div_of_nonneg_right
        (source_bound hn T hT hR hpi hsmall herr hthreshold hw b) (sq_nonneg _)
    _ ≤ ((K*(n : ℝ))*(diskConstant R)^2)/(n : ℝ)^2 := by gcongr
    _ = _ := by field_simp [ne_of_gt hnR] <;> ring

/-- The actual tournament score vector, embedded in the Euclidean space. -/
def scoreVector {n : ℕ} (T : Tournament (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 ((signMatrix T : Matrix (Fin n) (Fin n) ℂ).mulVec (fun _ => 1))

include hn hT hR hpi hsmall herr hthreshold hw in
theorem actual_score_bound {K : ℝ} (henergy : ‖scoreVector T‖^2 ≤ K*(n : ℝ)) :
    ‖⟪scoreVector T, (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
      ((resolventMatrix T w)⁻¹)) (scoreVector T)⟫_ℂ‖/(n : ℝ)^2 ≤
      K*(diskConstant R)^2/(n : ℝ) :=
  normalized_source_bound hn T hT hR hpi hsmall herr hthreshold hw (scoreVector T) henergy

/-- A single order threshold works simultaneously for every actual zero-diamond
tournament and every parameter in the closed disk. -/
theorem eventually_uniform_resolvent {r : ℝ} (hr : 0 ≤ r) (hrpi : r < Real.pi/2) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (T : Tournament (Fin n)), T.diamonds.card=0 →
      ∀ w : ℂ, ‖w‖ ≤ r →
        (resolventMatrix T w * (resolventMatrix T w)⁻¹=1 ∧
          (resolventMatrix T w)⁻¹ * resolventMatrix T w=1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) ((resolventMatrix T w)⁻¹)‖ ≤
          (diskConstant r)^2 := by
  filter_upwards [ComplexKernelDiskLower.eventually_thresholds hr hrpi] with n hn
  intro T hT w hw
  exact ⟨inverse_left_right hn.1 T hT hr hrpi hn.2.1 hn.2.2.1 hn.2.2.2 hw,
    inverse_operator_bound hn.1 T hT hr hrpi hn.2.1 hn.2.2.1 hn.2.2.2 hw⟩

/-- The normalized source estimate has one threshold uniform in the graph,
complex disk parameter, source vector and energy constant. -/
theorem eventually_uniform_source {r : ℝ} (hr : 0 ≤ r) (hrpi : r < Real.pi/2) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (T : Tournament (Fin n)), T.diamonds.card=0 →
      ∀ w : ℂ, ‖w‖ ≤ r → ∀ (b : EuclideanSpace ℂ (Fin n)) (K : ℝ),
        ‖b‖^2 ≤ K*(n : ℝ) →
        ‖⟪b, (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
          ((resolventMatrix T w)⁻¹)) b⟫_ℂ‖/(n : ℝ)^2 ≤
          K*(diskConstant r)^2/(n : ℝ) := by
  filter_upwards [ComplexKernelDiskLower.eventually_thresholds hr hrpi] with n hn
  intro T hT w hw b K henergy
  exact normalized_source_bound hn.1 T hT hr hrpi hn.2.1 hn.2.2.1 hn.2.2.2 hw b henergy

end DiamondFreeDiskResolvent
#print axioms DiamondFreeDiskResolvent.inverse_left_right
#print axioms DiamondFreeDiskResolvent.inverse_operator_bound
#print axioms DiamondFreeDiskResolvent.actual_score_bound

#print axioms DiamondFreeDiskResolvent.eventually_uniform_resolvent

#print axioms DiamondFreeDiskResolvent.eventually_uniform_source
