import WeightedCoefficientNorm

noncomputable section
namespace WeightedCoefficientProducts
open WeightedCoefficientNorm

theorem product {I : Type*} (s : Finset I) (F : I → PowerSeries ℂ) {rho : ℝ}
    (hr : 0≤rho) (hF : ∀i∈s,Finite rho (F i)) :
    Finite rho (∏i∈s,F i) ∧ norm rho (∏i∈s,F i)≤∏i∈s,norm rho (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,norm_one] using And.intro (finite_one rho) (le_refl (1:ℝ))
  | @insert a s ha ih =>
    have hs := ih (fun i hi => hF i (by simp [hi]))
    have haF := hF a (by simp)
    rw [Finset.prod_insert ha,Finset.prod_insert ha]
    exact ⟨finite_mul hr haF hs.1,(mul_bound hr haF hs.1).trans
      (mul_le_mul_of_nonneg_left hs.2 (norm_nonnegative hr _))⟩

theorem product_bound {I : Type*} (s : Finset I) (F : I → PowerSeries ℂ) {rho B : ℝ}
    (hr : 0≤rho) (hB : 0≤B) (hF : ∀i∈s,Finite rho (F i))
    (hb : ∀i∈s,norm rho (F i)≤B) : norm rho (∏i∈s,F i)≤B^s.card := by
  apply (product s F hr hF).2.trans
  calc
    _ ≤ ∏i∈s,B := Finset.prod_le_prod₀ (fun i hi => norm_nonnegative hr _) hb
    _ = _ := by simp

theorem analytic_bound {F : PowerSeries ℂ} {f : ℂ → ℂ} {rho s M : ℝ}
    (hr : 0≤rho) (hrs : rho<s) (hM : 0≤M)
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (fun k => F.coeff k)) 0)
    (hd : DiffContOnCl ℂ f (Metric.ball 0 s))
    (hb : ∀z∈Metric.sphere (0:ℂ) s,‖f z‖≤M) :
    Finite rho F ∧ norm rho F≤M/(1-rho/s) := by
  have ha := WickCoefficientCauchy.coefficient_bound hf (hr.trans_lt hrs) hd hb
  exact ⟨WickCoefficientCauchy.weighted_summable hr hrs hM ha,
    WickCoefficientCauchy.weighted_tsum_bound hr hrs hM ha⟩
end WeightedCoefficientProducts
#print axioms WeightedCoefficientProducts.product_bound
#print axioms WeightedCoefficientProducts.analytic_bound
