import MatrixScalingMassPotential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Bounds for an already existing actual scaling.
No existence assertion and no inference of an L2 estimate from an infinity estimate.
All energies are explicit finite sums of real squares. -/
set_option autoImplicit false
noncomputable section
namespace ScalingDensityFrobenius
open Finset MatrixScalingMassPotential
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Pointwise slope bound proved by the real mean value theorem. -/
theorem exp_sub_one_bound {b t : ℝ} (hb : 0 ≤ b) (ht : |t| ≤ b) :
    |Real.exp t - 1| ≤ Real.exp b * |t| := by
  have h0 : (0 : ℝ) ∈ Set.Icc (-b) b := ⟨by linarith, hb⟩
  have ht' : t ∈ Set.Icc (-b) b := abs_le.mp ht
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u ∈ Set.Icc (-b) b) => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u (hu : u ∈ Set.Icc (-b) b) => (show ‖Real.exp u‖ ≤ Real.exp b by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos u)]
      exact Real.exp_le_exp.mpr hu.2))
    (convex_Icc (-b) b) h0 ht'
  simpa [Real.norm_eq_abs] using hh

theorem sum_abs_bound (x : α → ℝ) (y : β → ℝ) {a : ℝ}
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) (i : α) (j : β) :
    |x i + y j| ≤ 2*a := by
  calc
    _ ≤ |x i| + |y j| := abs_add_le _ _
    _ ≤ 2*a := by linarith [hx i, hy j]

theorem scaled_density (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ)
    {a D : ℝ} (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ D)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) (i : α) (j : β) :
    0 ≤ expScaled M x y i j ∧ expScaled M x y i j ≤ Real.exp (2*a)*D := by
  refine ⟨expScaled_nonneg M x y hM i j, ?_⟩
  have ht : x i + y j ≤ 2*a := (le_abs_self _).trans (sum_abs_bound x y hx hy i j)
  unfold expScaled
  calc
    M i j * Real.exp (x i+y j) ≤ M i j * Real.exp (2*a) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht) (hM i j)
    _ ≤ D * Real.exp (2*a) := mul_le_mul_of_nonneg_right (hd i j) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- The density-to-weighted-square step loses no factor of the dimension. -/
theorem entry_square (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ)
    {a D : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ D)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) (i : α) (j : β) :
    (expScaled M x y i j - M i j)^2 ≤
      (2*D*Real.exp (4*a)) * (M i j * ((x i)^2+(y j)^2)) := by
  have ht := exp_sub_one_bound (by linarith : 0 ≤ 2*a) (sum_abs_bound x y hx hy i j)
  have hs : (Real.exp (x i+y j)-1)^2 ≤
      Real.exp (4*a)*(x i+y j)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))).mpr ht
    have he : (Real.exp (2*a))^2 = Real.exp (4*a) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [mul_pow, sq_abs, he] using hh
  have hm2 : (M i j)^2 ≤ D*M i j := by nlinarith [hM i j, hd i j]
  have hxy : (x i+y j)^2 ≤ 2*((x i)^2+(y j)^2) := by nlinarith [sq_nonneg (x i-y j)]
  have hdiff : expScaled M x y i j-M i j = M i j*(Real.exp (x i+y j)-1) := by
    unfold expScaled
    ring
  rw [hdiff, mul_pow]
  calc
    _ ≤ (D*M i j)*(Real.exp (4*a)*(x i+y j)^2) :=
      mul_le_mul hm2 hs (sq_nonneg _) (mul_nonneg hD (hM i j))
    _ ≤ (D*M i j)*(Real.exp (4*a)*(2*((x i)^2+(y j)^2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hxy (Real.exp_pos _).le) (mul_nonneg hD (hM i j))
    _ = _ := by ring

/-- Reordering is explicit: no row estimate is silently used for columns. -/
theorem weighted_square_sum (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ) :
    (∑ i, ∑ j, M i j*((x i)^2+(y j)^2)) =
      (∑ i, (∑ j, M i j)*(x i)^2) + (∑ j, (∑ i, M i j)*(y j)^2) := by
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]

theorem weighted_square_bound (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ)
    {S : ℝ} (hr : ∀ i, (∑ j, M i j) ≤ S) (hc : ∀ j, (∑ i, M i j) ≤ S) :
    (∑ i, ∑ j, M i j*((x i)^2+(y j)^2)) ≤
      S*((∑ i, (x i)^2)+(∑ j, (y j)^2)) := by
  rw [weighted_square_sum]
  calc
    _ ≤ (∑ i, S*(x i)^2)+(∑ j, S*(y j)^2) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hr i) (sq_nonneg _))
      · exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hc j) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum, mul_add]

/-- Squared Frobenius energy, with the independent input L2 energy preserved. -/
theorem frobenius_energy (M : Matrix α β ℝ) (x : α → ℝ) (y : β → ℝ)
    {a D S : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ D)
    (hr : ∀ i, (∑ j, M i j) ≤ S) (hc : ∀ j, (∑ i, M i j) ≤ S)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) :
    (∑ i, ∑ j, (expScaled M x y i j-M i j)^2) ≤
      (2*D*S*Real.exp (4*a))*((∑ i, (x i)^2)+(∑ j, (y j)^2)) := by
  have hcoef : 0 ≤ 2*D*Real.exp (4*a) := by positivity
  calc
    _ ≤ ∑ i, ∑ j, (2*D*Real.exp (4*a))*(M i j*((x i)^2+(y j)^2)) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _ => entry_square M x y ha hD hM hd hx hy i j)
    _ = (2*D*Real.exp (4*a))*(∑ i, ∑ j, M i j*((x i)^2+(y j)^2)) := by
      simp only [← Finset.mul_sum]
    _ ≤ (2*D*Real.exp (4*a))*(S*((∑ i, (x i)^2)+(∑ j, (y j)^2))) :=
      mul_le_mul_of_nonneg_left (weighted_square_bound M x y hr hc) hcoef
    _ = _ := by ring

/-- Exact 1/m coefficient for a square matrix with raw entry density C/m. -/
theorem frobenius_energy_fin {m : ℕ} (hm : 0 < m)
    (M : Matrix (Fin m) (Fin m) ℝ) (x y : Fin m → ℝ)
    {a C S : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ C/(m : ℝ))
    (hr : ∀ i, (∑ j, M i j) ≤ S) (hc : ∀ j, (∑ i, M i j) ≤ S)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ a) :
    (∑ i, ∑ j, (expScaled M x y i j-M i j)^2) ≤
      (2*C*S*Real.exp (4*a)/(m : ℝ))*((∑ i, (x i)^2)+(∑ j, (y j)^2)) := by
  have hh := frobenius_energy M x y ha (by positivity : 0 ≤ C/(m : ℝ)) hM hd hr hc hx hy
  convert hh using 1 <;> ring

end ScalingDensityFrobenius
#print axioms ScalingDensityFrobenius.exp_sub_one_bound
#print axioms ScalingDensityFrobenius.scaled_density
#print axioms ScalingDensityFrobenius.frobenius_energy_fin
