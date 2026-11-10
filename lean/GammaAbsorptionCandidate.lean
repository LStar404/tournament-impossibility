import ActualGammaBoundsCandidate
import GeneralScalarRestorationCandidate
set_option autoImplicit false
noncomputable section
namespace GammaAbsorptionCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open NonprincipalReconstructionCandidate

lemma sqrt_young {t n c : ℝ} (ht : 0 ≤ t) (hn : 0 < n) :
    c*Real.sqrt (t/n) ≤ t/4+c^2/n := by
  have hs := Real.sq_sqrt (div_nonneg ht hn.le)
  have hsq := sq_nonneg (Real.sqrt (t/n)*n-2*c)
  have hsn : (Real.sqrt (t/n)*n)^2 = t*n := by
    rw [mul_pow, hs]
    field_simp
  have heq : t/4+c^2/n = (t*n/4+c^2)/n := by field_simp
  rw [heq]
  apply (le_div_iff₀ hn).mpr
  nlinarith [hsq]

lemma exponent_absorption {t n c d eta E : ℝ} (k : ℕ)
    (ht : 0 ≤ t) (hn : 0 < n) (heta : eta ≤ 1/4)
    (hE : E ≤ eta*t+c*((k:ℝ)+1)*Real.sqrt (t/n)+d*((k:ℝ)+1)^2/n) :
    E ≤ t/2+(c^2+d)*((k:ℝ)+1)^2/n := by
  have hy := sqrt_young (c:=c*((k:ℝ)+1)) ht hn
  have he := mul_le_mul_of_nonneg_right heta ht
  have hident : (c*((k:ℝ)+1))^2/n+d*((k:ℝ)+1)^2/n =
      (c^2+d)*((k:ℝ)+1)^2/n := by ring
  linarith

lemma gamma_exp_absorption {G t E B : ℝ} (_hG : 0 ≤ G)
    (hupper : G ≤ Real.exp (-t)) (hE : E ≤ t/2+B) :
    G*Real.exp E ≤ Real.exp (-t/2+B) := by
  calc
    _ ≤ Real.exp (-t)*Real.exp (t/2+B) :=
      mul_le_mul hupper (Real.exp_le_exp.mpr hE) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma actual_gamma_exp_absorption {n : ℕ} (T : Tournament n) {a0 E B : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |normalizedScore T i| ≤ a0)
    (hE : E ≤ tau (normalizedScore T)/2+B) :
    gamma (normalizedScore T)*Real.exp E ≤ Real.exp (-tau (normalizedScore T)/2+B) := by
  exact gamma_exp_absorption (ActualGammaBoundsCandidate.gamma_pos _ a0 h0 h1 ha).le
    (ActualGammaBoundsCandidate.gamma_exp_bounds _ a0 h0 h1 ha).2 hE
end GammaAbsorptionCandidate
