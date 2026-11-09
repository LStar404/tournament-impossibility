import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Pi

/-! Verified construction. Genuine positive-measure one-coordinate moments,
not axioms about a formal Wick functional. -/
noncomputable section
namespace PermanentPositiveMoments
open MeasureTheory Set

lemma radial_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t)*t^k) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (k:ℝ)+1) (by positivity)
  simpa only [add_sub_cancel_right,Real.rpow_natCast] using h

/-- The radial exponential moment, with its integrability proved separately. -/
theorem radial_factorial (k : ℕ) :
    (∫ t in Ioi (0:ℝ), Real.exp (-t)*t^k) = (k.factorial:ℝ) := by
  have h := Real.Gamma_eq_integral (s := (k:ℝ)+1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  simpa only [add_sub_cancel_right,Real.rpow_natCast] using h.symm

local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

/-- Fourier characters are the integer powers of the unit-circle coordinate.
The Haar integral is positive and normalized; it is not a contour integral. -/
theorem phase_orthogonality (a b : ℤ) :
    (∫ t : AddCircle (1:ℝ),
      star (fourier b t) * fourier a t
      ∂AddCircle.haarAddCircle) = if a=b then (1:ℂ) else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1:ℝ)) a) b
  simpa [fourierCoeff,fourier_neg,smul_eq_mul,
    Pi.single_apply,eq_comm] using h

/-- Factorization across any finite collection of independent coordinates. -/
theorem finite_product_moments {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, E i → ℂ) :
    (∫ x : ∀ i, E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫ x, f i x ∂μ i := integral_fintype_prod_eq_prod f

end PermanentPositiveMoments
#print axioms PermanentPositiveMoments.radial_factorial
#print axioms PermanentPositiveMoments.phase_orthogonality
