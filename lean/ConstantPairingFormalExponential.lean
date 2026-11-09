import ConstantPairingMoments
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Expand

noncomputable section
namespace ConstantPairingFormalExponential
open ConstantPairingMoments

theorem rational_normalization (k : ℕ) :
    (pairFactor k : ℚ) * (1 / ((2*k).factorial : ℚ)) =
      (1/2 : ℚ)^k * (1 / (k.factorial : ℚ)) := by
  have h : (pairFactor k : ℚ) * 2^k * (k.factorial : ℚ) = ((2*k).factorial : ℚ) := by
    exact_mod_cast factor_factorial k
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2k : ((2*k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*k)
  rw [one_div_pow]
  field_simp
  nlinarith [h]

def actualSeries {S : Type*} [CommRing S] [Algebra ℚ S] (c : S) : PowerSeries S :=
  PowerSeries.mk (fun m => W m c * algebraMap ℚ S (1 / (m.factorial : ℚ)))

def target {S : Type*} [CommRing S] [Algebra ℚ S] (c : S) : PowerSeries S :=
  PowerSeries.expand 2 (by decide)
    (PowerSeries.rescale (algebraMap ℚ S (1/2) * c) (PowerSeries.exp S))

theorem coeff_even {S : Type*} [CommRing S] [Algebra ℚ S] (c : S) (k : ℕ) :
    (actualSeries c).coeff (2*k) = (target c).coeff (2*k) := by
  simp only [actualSeries,target,PowerSeries.coeff_mk,PowerSeries.coeff_expand_mul,
    PowerSeries.coeff_rescale,PowerSeries.coeff_exp,W_even]
  have h : (pairFactor k : S) * algebraMap ℚ S (1 / ((2*k).factorial : ℚ)) =
      algebraMap ℚ S ((1/2 : ℚ)^k * (1 / (k.factorial : ℚ))) := by
    rw [← map_natCast (algebraMap ℚ S) (pairFactor k), ← map_mul, rational_normalization]
  calc
    _ = c^k * ((pairFactor k : S) * algebraMap ℚ S (1 / ((2*k).factorial : ℚ))) := by ring
    _ = _ := by rw [h,map_mul,map_pow,mul_pow]; ring

theorem coeff_odd {S : Type*} [CommRing S] [Algebra ℚ S] (c : S) (k : ℕ) :
    (actualSeries c).coeff (2*k+1) = (target c).coeff (2*k+1) := by
  simp only [actualSeries,PowerSeries.coeff_mk,W_odd,zero_mul]
  symm
  apply PowerSeries.coeff_expand_of_not_dvd
  omega

/-- Formal power-series identity derived from actual full pairing moments.
No Gaussian measure or analytic convergence is asserted. -/
theorem actual_eq_exp {S : Type*} [CommRing S] [Algebra ℚ S] (c : S) :
    actualSeries c = target c := by
  ext m
  rcases Nat.even_or_odd m with ⟨k,hk⟩ | ⟨k,hk⟩
  · have he : m=2*k := by omega
    subst m
    simpa [two_mul] using coeff_even c k
  · have he : m=2*k+1 := by omega
    subst m
    exact coeff_odd c k

end ConstantPairingFormalExponential
#print axioms ConstantPairingFormalExponential.actual_eq_exp
