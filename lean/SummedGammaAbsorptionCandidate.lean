import GammaAbsorptionCandidate
set_option autoImplicit false
noncomputable section
namespace SummedGammaAbsorptionCandidate
open GammaAbsorptionCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open NonprincipalReconstructionCandidate

def budget (t n : ℝ) : ℝ := (t+t^2)/n+t*Real.sqrt (t/n)+Real.sqrt (t/n)+1/n

lemma budget_absorption {t n c E : ℝ} (ht : 0 ≤ t) (hn : 0 < n)
    (hsmall : c*((1+t)/n+Real.sqrt (t/n)) ≤ 1/4) (hE : E ≤ c*budget t n) :
    E ≤ t/2+(c^2+c)/n := by
  have he := mul_le_mul_of_nonneg_right hsmall ht
  have hy := sqrt_young (c:=c) ht hn
  have hid : c*budget t n = c*((1+t)/n+Real.sqrt (t/n))*t+c*Real.sqrt (t/n)+c/n := by
    unfold budget; ring
  rw [hid] at hE
  have hid2 : c^2/n+c/n=(c^2+c)/n := by ring
  linarith

lemma exp_linear_on_unit {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.exp b ≤ 1+Real.exp 1*b := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-b)) (Real.exp_pos b).le
  have he : Real.exp b * Real.exp (-b) = 1 := by rw [← Real.exp_add]; simp
  rw [he] at hh
  have hu := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb1) hb0
  nlinarith

lemma gamma_summed_decay {G t n c E : ℝ} (hG0 : 0 ≤ G) (hG : G ≤ Real.exp (-t))
    (ht : 0 ≤ t) (hn : 0 < n)
    (hsmall : c*((1+t)/n+Real.sqrt (t/n)) ≤ 1/4) (hE : E ≤ c*budget t n) :
    G*Real.exp E ≤ Real.exp (-t/2+(c^2+c)/n) :=
  gamma_exp_absorption hG0 hG (budget_absorption ht hn hsmall hE)

lemma gamma_summed_additive {G t n c E : ℝ} (hG0 : 0 ≤ G) (hG : G ≤ Real.exp (-t))
    (ht : 0 ≤ t) (hn : 0 < n) (hc : 0 ≤ c)
    (hsmall : c*((1+t)/n+Real.sqrt (t/n)) ≤ 1/4) (hE : E ≤ c*budget t n)
    (hb : (c^2+c)/n ≤ 1) :
    G*Real.exp E ≤ Real.exp (-t/2)+Real.exp 1*(c^2+c)/n := by
  have hd := gamma_summed_decay hG0 hG ht hn hsmall hE
  have hlin := exp_linear_on_unit (by positivity : 0 ≤ (c^2+c)/n) hb
  have ht' : Real.exp (-t/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.exp_add] at hd
  have hh := mul_le_mul_of_nonneg_left hlin (Real.exp_pos (-t/2)).le
  have hsmall2 := mul_le_mul_of_nonneg_right ht'
    (by positivity : 0 ≤ Real.exp 1*((c^2+c)/n))
  have hid : Real.exp 1*((c^2+c)/n)=Real.exp 1*(c^2+c)/n := by ring
  nlinarith

lemma actual_gamma_summed_additive {n : ℕ} (T : Tournament n) {a0 c E : ℝ}
    (hn : 0 < n) (h0 : 0 ≤ a0) (h1 : a0 < 1)
    (ha : ∀ i, |normalizedScore T i| ≤ a0) (hc : 0 ≤ c)
    (hsmall : c*((1+tau (normalizedScore T))/(n:ℝ)+Real.sqrt (tau (normalizedScore T)/(n:ℝ))) ≤ 1/4)
    (hE : E ≤ c*budget (tau (normalizedScore T)) n) (hb : (c^2+c)/(n:ℝ) ≤ 1) :
    gamma (normalizedScore T)*Real.exp E ≤ Real.exp (-tau (normalizedScore T)/2)+Real.exp 1*(c^2+c)/(n:ℝ) := by
  exact gamma_summed_additive (ActualGammaBoundsCandidate.gamma_pos _ a0 h0 h1 ha).le
    (ActualGammaBoundsCandidate.gamma_exp_bounds _ a0 h0 h1 ha).2 (tau_nonneg _) (by exact_mod_cast hn)
    hc hsmall hE hb
end SummedGammaAbsorptionCandidate
