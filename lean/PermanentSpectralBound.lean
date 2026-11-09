import PermanentEnergyIntegral
noncomputable section
namespace PermanentPositiveMoments
open MeasureTheory Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma density_real (x : I → RadialPhase) :
    density x = ((∏i, Real.exp (-(x i).1):ℝ):ℂ) := by simp [density]
lemma density_norm (x : I → RadialPhase) :
    ‖density x‖ = ∏i, Real.exp (-(x i).1) := by
  rw [density_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
lemma energy_re (s : I → ℝ) (m : ℕ) (x : I → RadialPhase) :
    (energyIntegrand s m x).re = (∏i, Real.exp (-(x i).1)) *
      (∑i,s i*‖coordinate (x i)‖^2)^m := by
  rw [energyIntegrand,density_real]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem spectral_permanent_bound {n : ℕ} (hn : 0<n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.permanent A‖ ≤ (n.factorial:ℝ)/(n:ℝ)^n *
      homogeneous (PermanentSpectralFrame.singularRoot A) n := by
  let s := PermanentSpectralFrame.singularRoot A
  let X := PermanentSpectralFrame.leftFactor A
  let Y := PermanentSpectralFrame.rightFactor A
  have hp : (∫ x, density x * linearProduct X x * star (linearProduct Y x) ∂productBase) =
      Matrix.permanent A := by
    rw [polarization, PermanentSpectralFrame.factors_reconstruct]
  have hbound : ∀x : Fin n → RadialPhase,
      ‖density x * linearProduct X x * star (linearProduct Y x)‖ ≤
      (energyIntegrand s n x).re / (n:ℝ)^n := by
    intro x
    have h := actual_pointwise hn A (fun i => coordinate (x i))
    change ‖linearProduct X x * star (linearProduct Y x)‖ ≤ _ at h
    rw [mul_assoc, norm_mul, energy_re, density_norm]
    rw [div_pow] at h
    calc
      _ ≤ (∏i, Real.exp (-(x i).1)) *
          ((∑i,s i*‖coordinate (x i)‖^2)^n/(n:ℝ)^n) :=
        mul_le_mul_of_nonneg_left h (Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))
      _ = _ := by ring
  have hi := (energy_integrable s n).re.div_const ((n:ℝ)^n)
  have hb := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hbound)
  rw [hp, integral_div, integral_re (energy_integrable s n), energy_integral] at hb
  change ‖Matrix.permanent A‖ ≤ ((n.factorial:ℂ)*(homogeneous s n:ℂ)).re/(n:ℝ)^n at hb
  simpa only [s, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero, mul_div_assoc,
    mul_comm, mul_left_comm, div_mul_eq_mul_div] using hb
end PermanentPositiveMoments
#print axioms PermanentPositiveMoments.spectral_permanent_bound
