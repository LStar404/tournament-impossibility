import MultivariateLinearFormalExponential
import Mathlib.RingTheory.PowerSeries.Derivative

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace RankOneQuadraticCoefficients
open OccurrenceWickPolynomial LinearSourceExpansion LinearSourcePairingFactor ConstantPairingMoments
variable {L S : Type*} [Fintype L] [Field S] [CharZero S]

def quadraticPolynomial (h : L → S) (a : S) : MvPolynomial L S :=
  (-a/2) • (source h)^2

def coefficient (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) (k : ℕ) : S :=
  wick C hs ((quadraticPolynomial h a)^k) / (k.factorial : S)

theorem coefficient_formula (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) (k : ℕ) :
    coefficient C hs h a k =
      (-a/2)^k * (pairFactor k : S) * (quadratic C h)^k / (k.factorial : S) := by
  unfold coefficient quadraticPolynomial
  rw [smul_pow, map_smul, ← pow_mul, MultivariateLinearFormalExponential.wick_power, W_even]
  simp only [smul_eq_mul]
  ring

theorem coefficient_zero (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) : coefficient C hs h a 0 = 1 := by
  simp [coefficient_formula, pairFactor]

theorem coefficient_step (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) (k : ℕ) :
    (k+1:S) * coefficient C hs h a (k+1) =
      -(a * quadratic C h)/2 * (2*k+1:S) * coefficient C hs h a k := by
  rw [coefficient_formula, coefficient_formula, pairFactor_step, Nat.factorial_succ]
  push_cast
  rw [pow_succ, pow_succ]
  have hk : (k.factorial : S) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk1 : (k:S)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp
  <;> ring

def series (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) : PowerSeries S :=
  PowerSeries.mk (coefficient C hs h a)

@[simp] theorem coeff_series (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) (k : ℕ) :
    (series C hs h a).coeff k = coefficient C hs h a k := by
  simp [series]

@[simp] theorem constant_series (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (a : S) : (series C hs h a).constantCoeff = 1 := by
  simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using coefficient_zero C hs h a

end RankOneQuadraticCoefficients
#print axioms RankOneQuadraticCoefficients.coefficient_step
