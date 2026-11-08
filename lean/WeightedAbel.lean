import Descent
import Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace NonAlgebraicity
open scoped BigOperators
open PowerSeries Filter Topology

theorem rescale_C' {K : Type*} [Field K] (a c : K) :
    rescale a (C c) = C c := by
  ext k
  by_cases hk : k = 0 <;> simp [coeff_C, hk]

theorem rescale_smul' {K : Type*} [Field K] (a c : K) (B : PowerSeries K) :
    rescale a (c • B) = c • rescale a B := by
  simp only [smul_eq_C_mul, map_mul, rescale_C']

/-- Invertible variable rescaling preserves polynomial relations. -/
theorem relation_rescale {K : Type*} [Field K] (B : PowerSeries K)
    {a : K} (ha : a ≠ 0) (h : HasPolynomialRelation B) :
    HasPolynomialRelation (rescale a B) := by
  classical
  obtain ⟨m, n, c, hc, hrel⟩ := h
  refine ⟨m, n, fun ij => c ij * a ^ ij.1.val, ?_, ?_⟩
  · intro hz
    apply hc
    funext ij
    have hh := congrFun hz ij
    exact (mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ ha)
  · have hh := congrArg (rescale a) hrel
    simp only [map_sum, map_zero, rescale_smul', map_mul, map_pow, rescale_X] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro ij _
    simp only [smul_eq_C_mul, map_mul, map_pow, mul_pow]
    ring

/-- A nonzero scalar multiple cannot acquire an algebraic relation. -/
theorem relation_of_smul {K : Type*} [Field K] (B : PowerSeries K)
    {a : K} (ha : a ≠ 0) (h : HasPolynomialRelation (a • B)) :
    HasPolynomialRelation B := by
  classical
  obtain ⟨m, n, c, hc, hrel⟩ := h
  refine ⟨m, n, fun ij => c ij * a ^ ij.2.val, ?_, ?_⟩
  · intro hz
    apply hc
    funext ij
    have hh := congrFun hz ij
    exact (mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ ha)
  · convert hrel using 1
    apply Finset.sum_congr rfl
    intro ij _
    simp only [smul_eq_C_mul, map_mul, map_pow, mul_pow]
    ring

/-- The exact transformation E(z)=b*A(a*z), for nonzero a and b. -/
theorem no_relation_rescale_smul {K : Type*} [Field K] (B : PowerSeries K)
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hB : ¬ HasPolynomialRelation B) :
    ¬ HasPolynomialRelation (b • rescale a B) := by
  intro h
  have hh := relation_rescale (b • rescale a B) (inv_ne_zero ha) h
  rw [rescale_smul', rescale_rescale, mul_inv_cancel₀ ha, rescale_one] at hh
  exact hB (relation_of_smul B hb hh)

/-- In particular, E(z)=2*A(z/2) is nonalgebraic whenever A is. -/
theorem exponential_gf_non_algebraic (B : PowerSeries ℂ)
    (hB : ¬ HasPolynomialRelation B) :
    ¬ HasPolynomialRelation ((2 : ℂ) • rescale (1 / 2 : ℂ) B) := by
  exact no_relation_rescale_smul B (by norm_num) (by norm_num) hB

#print axioms exponential_gf_non_algebraic
end NonAlgebraicity
