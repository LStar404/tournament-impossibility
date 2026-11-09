import PermanentPointwiseAMGM
import Mathlib.Data.Nat.Choose.Multinomial
noncomputable section
namespace PermanentPositiveMoments
open MeasureTheory
variable {I : Type*} [Fintype I] [DecidableEq I]
def homogeneous (s : I → ℝ) (m : ℕ) : ℝ :=
  ∑ k∈Finset.piAntidiag Finset.univ m, ∏i, (s i)^k i

def energyIntegrand (s : I → ℝ) (m : ℕ) (x : I → RadialPhase) : ℂ :=
  density x * ((∑i,s i*‖coordinate (x i)‖^2 : ℝ):ℂ)^m

lemma diagonal_monomial (k : I → ℕ) (x : I → RadialPhase) :
    mixedMonomial k k x = density x * ∏i, ((‖coordinate (x i)‖^2:ℝ):ℂ)^k i := by
  rw [← density_monomial]
  rw [mul_assoc, star_prod, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [star_pow, ← mul_pow, Complex.star_def, Complex.mul_conj']
  norm_cast

lemma energy_expansion (s : I → ℝ) (m : ℕ) (x : I → RadialPhase) :
    energyIntegrand s m x = ∑ k∈Finset.piAntidiag Finset.univ m,
      ((Nat.multinomial Finset.univ k:ℂ)*∏i,(s i:ℂ)^k i)* mixedMonomial k k x := by
  unfold energyIntegrand
  push_cast
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [diagonal_monomial]
  simp only [mul_pow, Finset.prod_mul_distrib, Complex.ofReal_pow]
  ring

lemma energy_integrable (s : I → ℝ) (m : ℕ) :
    Integrable (energyIntegrand s m) productBase := by
  change Integrable (fun x => energyIntegrand s m x) productBase
  simp_rw [energy_expansion]
  exact integrable_finsetSum _ (fun k hk => (mixedMonomial_integrable k k).const_mul _)

theorem energy_integral (s : I → ℝ) (m : ℕ) :
    (∫ x, energyIntegrand s m x ∂productBase) = (m.factorial:ℂ)*(homogeneous s m:ℂ) := by
  simp_rw [energy_expansion]
  rw [finite_mixed_integral]
  simp only [ite_true]
  unfold homogeneous
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hc := Nat.multinomial_spec Finset.univ k
  rw [(Finset.mem_piAntidiag.mp hk).1] at hc
  have hcc : (∏i, ((k i).factorial:ℂ))*(Nat.multinomial Finset.univ k:ℂ)=(m.factorial:ℂ) := by
    exact_mod_cast hc
  calc
    _ = ((∏i, ((k i).factorial:ℂ))*(Nat.multinomial Finset.univ k:ℂ))*(∏i, (s i:ℂ)^k i) := by ring
    _ = _ := by rw [hcc]
end PermanentPositiveMoments
#print axioms PermanentPositiveMoments.energy_integral
