import UnitScoreLogFactorCandidate
set_option autoImplicit false
noncomputable section
namespace UnitScorePotentialBudgetCandidate
open UnitScorePrefactorCandidate

def thetaConstant : ℝ := (2*Real.exp (1/2)/(7/184))*1460^2+1860
def fullConstant : ℝ := thetaConstant+70

lemma finite_theta_budget {n m t ε k θ : ℝ}
    (hn : 0<n) (hm : 0 < m) (hmn : m≤n) (ht : 0≤t)
    (hε : 0≤ε) (he : ε≤1460*(t+1)/n)
    (hk : |k|≤930*(t+1)^2/n) (hkhalf : |k|≤ m/2)
    (hθ0 : 0≤θ) (hθ : θ≤(2*Real.exp (1/2)/(7/184))*m*ε^2) :
    |θ+m*Real.log (m/(m+k))|≤thetaConstant*(t+1)^2/n := by
  have hc : 0≤2*Real.exp (1/2)/(7/184) := by positivity
  have hsq : ε^2≤(1460*(t+1)/n)^2 := pow_le_pow_left₀ hε he 2
  have he2 : m*ε^2≤1460^2*(t+1)^2/n := by
    calc
      _ ≤ n*ε^2 := mul_le_mul_of_nonneg_right hmn (sq_nonneg _)
      _ ≤ n*(1460*(t+1)/n)^2 := mul_le_mul_of_nonneg_left hsq hn.le
      _ = _ := by field_simp
  have hθ' : θ≤(2*Real.exp (1/2)/(7/184))*1460^2*(t+1)^2/n := by
    have hh := mul_le_mul_of_nonneg_left he2 hc
    simp only [div_eq_mul_inv] at hθ hh ⊢
    nlinarith only [hθ, hh]
  have hs := shifted_potential_abs_bound hm hkhalf hθ0 hθ'
  unfold thetaConstant
  simp only [div_eq_mul_inv] at hs hk ⊢
  nlinarith only [hs,hk]
end UnitScorePotentialBudgetCandidate
