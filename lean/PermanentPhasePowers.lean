import PermanentPositiveMoments

/-! Actual phase powers and fractional radial integrability. -/
noncomputable section
namespace PermanentPositiveMoments
open MeasureTheory
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

/-- Actual powers of the unit-circle coordinate, not a definition by desired moments. -/
theorem phase_power (a : ℕ) (t : AddCircle (1:ℝ)) :
    (fourier 1 t)^a = fourier (a:ℤ) t := by
  induction a with
  | zero => simp
  | succ a ha =>
    rw [pow_succ, ha]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (fourier_add (m := (a:ℤ)) (n := 1) (x := t)).symm

theorem phase_mixed_moment (a b : ℕ) :
    (∫ t : AddCircle (1:ℝ),
      (fourier 1 t)^a * star ((fourier 1 t)^b)
      ∂AddCircle.haarAddCircle) = if a=b then (1:ℂ) else 0 := by
  simp_rw [phase_power]
  simpa only [mul_comm, Nat.cast_inj] using
    phase_orthogonality (a:ℤ) (b:ℤ)

/-- Absolute mixed radial monomials require half-integer, not just integer, moments. -/
theorem radial_fractional_integrable (a b : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t)*t^(((a:ℝ)+(b:ℝ))/2)) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent
    (s := ((a:ℝ)+(b:ℝ))/2+1) (by positivity)
  simpa only [add_sub_cancel_right] using h

end PermanentPositiveMoments
#print axioms PermanentPositiveMoments.phase_mixed_moment
#print axioms PermanentPositiveMoments.radial_fractional_integrable
