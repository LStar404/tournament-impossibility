import ActualTournamentDisplacementCandidate
/-! Isolated finite rate proof. Actual scalar budgets only. -/
set_option autoImplicit false
noncomputable section
namespace ActualNormalizationRateCandidate
open Matrix Finset Filter
open scoped Topology
open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization
open TournamentPrescalingMassBound DeletedScalingSynthesisCandidate
open RealBilinearTrace RealGramEndpoint LogWindowFrobeniusUniformCandidate
variable {n : ℕ}

def rate (T : Tournament n) (t : ℕ) : ℝ :=
  Real.sqrt (tau (normalizedScore T)/(n:ℝ))+((t:ℝ)+1)/(n:ℝ)
def deltaConstant (a0 : ℝ) := 16*(scaleCap a0)^2+4
def displacementConstant (a0 : ℝ) :=
  Real.sqrt (fixedCoefficient a0)*(6*deltaConstant a0+4*(16*(scaleCap a0)^2+1))+
  80*(scaleCap a0)^2+4+8*deltaConstant a0+4*(16*(scaleCap a0)^2+1)

lemma rate_components (T : Tournament n) (t : ℕ) (hn : 0 < n) :
    0 ≤ rate T t ∧ Real.sqrt (tau (normalizedScore T)/(n:ℝ)) ≤ rate T t ∧
    (1:ℝ)/(n:ℝ) ≤ rate T t ∧ (t:ℝ)/(n:ℝ) ≤ rate T t := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have ht : (0:ℝ)≤t := Nat.cast_nonneg _
  have hs := Real.sqrt_nonneg (tau (normalizedScore T)/(n:ℝ))
  unfold rate
  constructor
  · positivity
  constructor
  · have hh : 0≤((t:ℝ)+1)/(n:ℝ) := by positivity
    linarith
  constructor
  · have hh := div_le_div_of_nonneg_right (show (1:ℝ)≤(t:ℝ)+1 by linarith) hnR.le
    linarith
  · have hh := div_le_div_of_nonneg_right (show (t:ℝ)≤(t:ℝ)+1 by linarith) hnR.le
    linarith

lemma actual_delta_rate (T : Tournament n) (t : ℕ) (hn : 0 < n) (a0 : ℝ)
    (hM : massBound T a0 ≤ 1) :
    normalizedMarginalBound T a0 ≤ deltaConstant a0*rate T t := by
  have hc := rate_components T t hn
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have he : Real.sqrt (tau (normalizedScore T))/Real.sqrt (n:ℝ) =
      Real.sqrt (tau (normalizedScore T)/(n:ℝ)) := (Real.sqrt_div (tau_nonneg _) _).symm
  unfold normalizedMarginalBound deltaConstant
  simp only [mul_div_assoc, he]
  have hm := div_le_div_of_nonneg_right hM hnR.le
  have hs := mul_le_mul_of_nonneg_left hc.2.1 (show 0≤16*(scaleCap a0)^2 by positivity)
  nlinarith [hc.2.2.1]

lemma actual_fnorm_rate (T : Tournament n) (t : ℕ) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |normalizedScore T i| ≤ a0)
    (hM : massBound T a0 ≤ 1) :
    fnorm (normalizedMatrix T-baseMatrix T) ≤ 40*(scaleCap a0)^2*rate T t := by
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hc := rate_components T t hn0
  have hs := Real.sq_sqrt (div_nonneg (tau_nonneg (normalizedScore T)) hnR.le)
  have hb := normalized_frobenius_bound T hn h0 h1 ha
  have hf := fnorm_sq (normalizedMatrix T-baseMatrix T)
  have hM0 := massBound_nonneg T a0
  have hMs : (massBound T a0)^2 ≤ 1 := by nlinarith
  have hs1 : tau (normalizedScore T)/(n:ℝ) ≤ (rate T t)^2 := by
    nlinarith [Real.sqrt_nonneg (tau (normalizedScore T)/(n:ℝ))]
  have hs2 : ((1:ℝ)/(n:ℝ))^2 ≤ (rate T t)^2 := by
    nlinarith [div_nonneg (show (0:ℝ)≤1 by norm_num) hnR.le]
  have h1b := mul_le_mul_of_nonneg_left hs1 (show 0≤128*(scaleCap a0)^4 by positivity)
  have h2b := mul_le_mul_of_nonneg_left hs2 (show 0≤512*(scaleCap a0)^4 by positivity)
  have hMb := mul_le_mul_of_nonneg_left hMs
    (show 0≤512*(scaleCap a0)^4/(n:ℝ)^2 by positivity)
  have hbf : fnorm (normalizedMatrix T-baseMatrix T)^2 ≤
      640*(scaleCap a0)^4*(rate T t)^2 := by
    simp only [frob, Matrix.sub_apply] at hf
    have he : 512*(scaleCap a0)^4/(n:ℝ)^2 = 512*(scaleCap a0)^4*((1:ℝ)/(n:ℝ))^2 := by ring
    rw [he] at hMb
    simp only [div_eq_mul_inv, ← inv_pow] at hb h1b h2b hMb
    nlinarith only [hb, hf, h1b, h2b, hMb]
  have hf0 : 0 ≤ fnorm (normalizedMatrix T-baseMatrix T) := norm_nonneg _
  have hr0 := hc.1
  have hp : 0 ≤ 40*(scaleCap a0)^2*rate T t := by positivity
  nlinarith [sq_nonneg ((scaleCap a0)^2*rate T t)]

lemma finite_budget_rate (T : Tournament n) (t m : ℕ) (hn : 0 < n) (a0 : ℝ)
    (htn : (t:ℝ) ≤ (n:ℝ)/2) (hM : massBound T a0 ≤ 1)
    (K : ℝ) (hK : K=4*(t:ℝ)*normalizedMarginalBound T a0+
      2*(16*(scaleCap a0)^2+1)*(t:ℝ)^2/(n:ℝ))
    (hgap : (n:ℝ)/2 ≤ (m:ℝ)-K) :
    Real.sqrt (fixedCoefficient a0)*residualBudget n m t
      (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) K+
      80*(scaleCap a0)^2*rate T t+4*((t:ℝ)+K)/(n:ℝ) ≤
      displacementConstant a0*rate T t := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hc := rate_components T t hn
  have hd := actual_delta_rate T t hn a0 hM
  have hk := NormalizationScalarsCandidate.K_budget hnR (Nat.cast_nonneg t) htn
    (show 0≤16*(scaleCap a0)^2 by positivity) (normalizedMarginalBound_nonneg T a0) hK
  have he := (NormalizationScalarsCandidate.epsilon_budget hnR (Nat.cast_nonneg t)
    (show 0≤16*(scaleCap a0)^2 by positivity) (normalizedMarginalBound_nonneg T a0)
    hk.1 hgap hk.2).2
  change residualBudget n m t (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) K ≤ _ at he
  have ht := mul_le_mul_of_nonneg_left hc.2.2.2 (show 0≤16*(scaleCap a0)^2+1 by positivity)
  have he' : residualBudget n m t (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) K ≤
      (6*deltaConstant a0+4*(16*(scaleCap a0)^2+1))*rate T t := by
    simp only [div_eq_mul_inv] at he ht
    nlinarith only [he, ht, hd]
  have hes := mul_le_mul_of_nonneg_left he' (Real.sqrt_nonneg (fixedCoefficient a0))
  unfold displacementConstant
  have hkb := hk.2
  have htr := hc.2.2.2
  simp only [div_eq_mul_inv] at hkb ht htr ⊢
  nlinarith only [hes, hd, ht, hkb, htr]
end ActualNormalizationRateCandidate
