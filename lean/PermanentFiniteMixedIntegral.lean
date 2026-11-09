import PermanentRadialPhaseMoment

/-! Verified construction. Actual finite mixed-polynomial integrals. -/
noncomputable section
namespace PermanentPositiveMoments
open MeasureTheory
variable {I : Type*} [Fintype I] [DecidableEq I]
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
instance baseSigmaFinite : SigmaFinite baseMeasure := by
  unfold baseMeasure
  infer_instance

def productBase : Measure (I → RadialPhase) := Measure.pi (fun _ => baseMeasure)
def mixedMonomial (a b : I → ℕ) (x : I → RadialPhase) : ℂ :=
  ∏ i, mixedIntegrand (a i) (b i) (x i)

theorem mixedMonomial_integrable (a b : I → ℕ) :
    Integrable (mixedMonomial a b) productBase :=
  Integrable.fintype_prod (fun i => mixed_integrable (a i) (b i))

theorem mixedMonomial_integral (a b : I → ℕ) :
    (∫ x, mixedMonomial a b x ∂productBase) =
      if a=b then ∏ i, ((a i).factorial:ℂ) else 0 := by
  unfold mixedMonomial productBase
  rw [integral_fintype_prod_eq_prod]
  simp_rw [mixed_moment]
  by_cases hab : a=b
  · subst b
    simp
  · simp only [hab, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- A finite arbitrary mixed-polynomial expression is integrated term by term only
 after absolute integrability of every actual term has been established. -/
theorem finite_mixed_integral {J : Type*} (s : Finset J) (c : J → ℂ)
    (a b : J → I → ℕ) :
    (∫ x, ∑ j∈s, c j * mixedMonomial (a j) (b j) x ∂productBase) =
      ∑ j∈s, c j * (if a j=b j then ∏ i, ((a j i).factorial:ℂ) else 0) := by
  rw [integral_finset_sum s (fun j hj => (mixedMonomial_integrable (a j) (b j)).const_mul (c j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, mixedMonomial_integral]
end PermanentPositiveMoments
#print axioms PermanentPositiveMoments.finite_mixed_integral
