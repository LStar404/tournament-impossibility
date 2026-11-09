import AnalyticNormalizedBranch

noncomputable section
namespace AnalyticTaylorArithmetic

def series (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => iteratedDeriv n f 0 / (n.factorial:ℂ))

@[simp] theorem coeff_series (f : ℂ → ℂ) (n : ℕ) :
    (series f).coeff n=iteratedDeriv n f 0/(n.factorial:ℂ) := PowerSeries.coeff_mk _ _

theorem hasSeries {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (fun n => (series f).coeff n)) 0 := by
  simpa only [coeff_series] using hf.hasFPowerSeriesAt

theorem congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) : series f=series g := by
  ext n
  rw [coeff_series,coeff_series,h.iteratedDeriv_eq]

@[simp] theorem constant (c : ℂ) : series (fun _ => c)=PowerSeries.C c := by
  ext n
  by_cases h : n=0
  · subst n; simp [coeff_series]
  · simp [coeff_series,iteratedDeriv_const,PowerSeries.coeff_C,h]

@[simp] theorem initial (f : ℂ → ℂ) : (series f).constantCoeff=f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,coeff_series]
  simp

theorem add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    series (f+g)=series f+series g := by
  ext n
  simp only [coeff_series,map_add,iteratedDeriv_add hf.contDiffAt hg.contDiffAt,add_div]

lemma choose_factor (n i : ℕ) (hi : i≤n) :
    (n.choose i:ℂ)/(n.factorial:ℂ)=1/((i.factorial:ℂ)*((n-i).factorial:ℂ)) := by
  have hh : (n.choose i:ℂ)*(i.factorial:ℂ)*((n-i).factorial:ℂ)=(n.factorial:ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hi' : (i.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : ((n-i).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (n-i)
  field_simp
  exact hh

theorem mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    series (f*g)=series f*series g := by
  ext n
  rw [coeff_series,iteratedDeriv_mul hf.contDiffAt hg.contDiffAt,Finset.sum_div,
    PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coeff_series]
  have hc := choose_factor n i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  calc
    _ = ((n.choose i:ℂ)/(n.factorial:ℂ))*iteratedDeriv i f 0*iteratedDeriv (n-i) g 0 := by ring
    _ = _ := by rw [hc]; ring

end AnalyticTaylorArithmetic
#print axioms AnalyticTaylorArithmetic.mul
#print axioms AnalyticTaylorArithmetic.hasSeries
