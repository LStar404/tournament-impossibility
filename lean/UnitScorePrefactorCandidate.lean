import ActualSameRootPotentialCandidate
import ActualGammaBoundsCandidate
/-! Verified finite bookkeeping; actual specialization is in ActualUnitScorePrefactorCandidate. -/
set_option autoImplicit false
noncomputable section
namespace UnitScorePrefactorCandidate
open Matrix Finset TournamentHamiltonian ActualTournamentPrescalingBounds
open ActualPrescalingNormalization ActualRecoveryUpperCandidate PhysicalMinorRecoveryCandidate
open NonprincipalReconstructionCandidate SameRootPotentialCandidate MatrixScalingMassPotential
variable {n m : ℕ}

def referenceScale (n m : ℕ) : ℝ := ((m:ℝ)*((n:ℝ)-1)/(2*(n:ℝ)))^m

def fullPrefactor (T : Tournament n) (I : Finset (Fin n)) (x y : Fin m → ℝ) : ℝ :=
  (∏ i∈Iᶜ, (1-(normalizedScore T i)^2))*
    (1+nu T/(n:ℝ))^m*Real.exp (-shiftedPotential T I I x y)

lemma exact_full_prefactor (T : Tournament n) (I : Finset (Fin n)) (x y : Fin m → ℝ)
    (hn : 0<n) (ha : ∀ i, |normalizedScore T i|<1) :
    recoveryFactor T I I m*Real.exp (-shiftedPotential T I I x y)=
      referenceScale n m*fullPrefactor T I x y := by
  have hnR : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs : (m:ℝ)*((n:ℝ)-1)*((n:ℝ)+nu T)/(2*(n:ℝ)^2)=
      ((m:ℝ)*((n:ℝ)-1)/(2*(n:ℝ)))*(1+nu T/(n:ℝ)) := by
    field_simp
  unfold recoveryFactor
  rw [principal_retained_gamma (normalizedScore T) I ha, hs, mul_pow]
  unfold referenceScale fullPrefactor
  ring

lemma log_one_add_abs {u : ℝ} (hu : |u|≤1/2) :
    |Real.log (1+u)|≤2*|u| := by
  have hab := abs_le.mp hu
  have hp : 0<1+u := by linarith
  have hlo := Real.one_sub_inv_le_log_of_pos hp
  have hhi := Real.log_le_sub_one_of_pos hp
  have he : 1-(1+u)⁻¹=u/(1+u) := by field_simp; ring
  rw [he] at hlo
  have hl : -2*|u|≤u/(1+u) := by
    apply (le_div_iff₀ hp).mpr
    have hu' := neg_abs_le u
    have ha := abs_nonneg u
    nlinarith
  apply abs_le.mpr
  constructor
  · linarith [hl.trans hlo]
  · linarith [le_abs_self u, abs_nonneg u]

lemma physical_shift_bound {d k : ℝ} (hd : 0<d) (hk : |k|≤d/2) :
    |d*Real.log (d/(d+k))|≤2*|k| := by
  have hp : 0<d+k := by linarith [(abs_le.mp hk).1]
  have hu : |k/d|≤1/2 := by
    rw [abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).mpr (by linarith)
  have he : d/(d+k)=(1+k/d)⁻¹ := by field_simp
  rw [he, Real.log_inv, abs_mul, abs_neg, abs_of_pos hd]
  have hh := mul_le_mul_of_nonneg_left (log_one_add_abs hu) hd.le
  rw [abs_div, abs_of_pos hd] at hh
  calc
    _ ≤ d*(2*(|k|/d)) := hh
    _ = _ := by field_simp

lemma shifted_potential_abs_bound {theta d k H : ℝ}
    (hd : 0<d) (hk : |k|≤d/2) (ht0 : 0≤theta) (htH : theta≤H) :
    |theta+d*Real.log (d/(d+k))|≤H+2*|k| := by
  calc
    _ ≤ |theta|+|d*Real.log (d/(d+k))| := abs_add_le _ _
    _ ≤ H+2*|k| := by rw [abs_of_nonneg ht0]; exact add_le_add htH (physical_shift_bound hd hk)
end UnitScorePrefactorCandidate
