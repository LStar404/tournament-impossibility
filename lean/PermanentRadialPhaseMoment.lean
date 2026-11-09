import PermanentPhasePowers
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual construction: a genuine positive radial-phase product model. -/
noncomputable section
namespace PermanentPositiveMoments
open MeasureTheory Set
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
abbrev RadialPhase := ℝ × AddCircle (1:ℝ)
def baseMeasure : Measure RadialPhase :=
  (volume.restrict (Ioi (0:ℝ))).prod AddCircle.haarAddCircle

def coordinate (x : RadialPhase) : ℂ :=
  (x.1 ^ (1/2:ℝ) : ℝ) * fourier 1 x.2

def mixedIntegrand (a b : ℕ) (x : RadialPhase) : ℂ :=
  (Real.exp (-x.1) : ℂ) * coordinate x ^ a * star (coordinate x ^ b)

def separatedIntegrand (a b : ℕ) (x : RadialPhase) : ℂ :=
  (Real.exp (-x.1)*x.1^(((a:ℝ)+(b:ℝ))/2) : ℝ) *
    ((fourier 1 x.2)^a * star ((fourier 1 x.2)^b))

lemma mixed_eq_separated (a b : ℕ) (x : RadialPhase) (ht : 0 < x.1) :
    mixedIntegrand a b x = separatedIntegrand a b x := by
  have hp : (x.1^(1/2:ℝ))^a * (x.1^(1/2:ℝ))^b =
      x.1^(((a:ℝ)+(b:ℝ))/2) := by
    rw [← Real.rpow_mul_natCast ht.le, ← Real.rpow_mul_natCast ht.le,
      ← Real.rpow_add ht]
    congr 1
    ring
  have hpc : ((x.1^(1/2:ℝ):ℝ):ℂ)^a * ((x.1^(1/2:ℝ):ℝ):ℂ)^b =
      (x.1^(((a:ℝ)+(b:ℝ))/2):ℝ) := by exact_mod_cast hp
  unfold mixedIntegrand coordinate separatedIntegrand
  simp only [mul_pow, star_mul, star_pow, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  calc
    _ = (Real.exp (-x.1):ℂ) *
        (((x.1^(1/2:ℝ):ℝ):ℂ)^a * ((x.1^(1/2:ℝ):ℝ):ℂ)^b) *
        ((fourier 1 x.2)^a * star (fourier 1 x.2)^b) := by simp only [Complex.star_def]; ring
    _ = _ := by rw [hpc]; simp only [Complex.star_def]

lemma separated_integrable (a b : ℕ) : Integrable (separatedIntegrand a b) baseMeasure := by
  have hr := (radial_fractional_integrable a b).ofReal (𝕜 := ℂ)
  have hc : Continuous (fun t : AddCircle (1:ℝ) =>
      (fourier 1 t)^a * star ((fourier 1 t)^b)) := by fun_prop
  have hi : Integrable (fun t : AddCircle (1:ℝ) =>
      (fourier 1 t)^a * star ((fourier 1 t)^b))
      AddCircle.haarAddCircle := by
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  exact hr.mul_prod hi

/-- This proof computes the actual positive product integral, not a formal moment axiom. -/
theorem separated_moment (a b : ℕ) :
    (∫ x, separatedIntegrand a b x ∂baseMeasure) =
      if a=b then (a.factorial:ℂ) else 0 := by
  unfold separatedIntegrand baseMeasure
  rw [show (∫ x : RadialPhase,
      ((Real.exp (-x.1)*x.1^(((a:ℝ)+(b:ℝ))/2):ℝ):ℂ) *
      ((fourier 1 x.2)^a * star ((fourier 1 x.2)^b))
      ∂(volume.restrict (Ioi (0:ℝ))).prod AddCircle.haarAddCircle) = _ from
    integral_prod_mul
      (fun t : ℝ => ((Real.exp (-t)*t^(((a:ℝ)+(b:ℝ))/2):ℝ):ℂ))
      (fun t : AddCircle (1:ℝ) => (fourier 1 t)^a * star ((fourier 1 t)^b))]
  rw [phase_mixed_moment]
  by_cases hab : a=b
  · subst b
    simp only [ite_true, mul_one]
    rw [integral_complex_ofReal]
    have he : ((a:ℝ)+(a:ℝ))/2 = (a:ℝ) := by ring
    simp_rw [he, Real.rpow_natCast]
    rw [radial_factorial]
    norm_cast
  · simp [hab]

lemma mixed_ae_separated (a b : ℕ) :
    mixedIntegrand a b =ᵐ[baseMeasure] separatedIntegrand a b := by
  have ht : ∀ᵐ x ∂baseMeasure, x.1 ∈ Ioi (0:ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [ht] with x hx
  exact mixed_eq_separated a b x hx

 theorem mixed_integrable (a b : ℕ) : Integrable (mixedIntegrand a b) baseMeasure :=
  (separated_integrable a b).congr (mixed_ae_separated a b).symm

 theorem mixed_moment (a b : ℕ) :
    (∫ x, mixedIntegrand a b x ∂baseMeasure) =
      if a=b then (a.factorial:ℂ) else 0 := by
  rw [integral_congr_ae (mixed_ae_separated a b), separated_moment]
end PermanentPositiveMoments
#print axioms PermanentPositiveMoments.mixed_moment
