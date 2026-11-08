import Radial
import Mathlib.Tactic

open Polynomial Filter Topology
namespace NonAlgebraicity

/-- A finite limit of a rational function over ℚ at 1 is rational. Common
endpoint factors are removed recursively; no denominator-nonvanishing
assumption at the endpoint is imposed. -/
theorem rational_limit_of_linear_relation {α : Type*} {l : Filter α} [NeBot l]
    {x y : α → ℂ} {c : ℂ}
    (hx : Tendsto x l (𝓝 1)) (hy : Tendsto y l (𝓝 c))
    (hne : ∀ᶠ t in l, x t ≠ 1)
    (P Q : ℚ[X]) (hP : P ≠ 0)
    (hrel : ∀ᶠ t in l,
      P.eval₂ (algebraMap ℚ ℂ) (x t) * y t = Q.eval₂ (algebraMap ℚ ℂ) (x t)) :
    ∃ r : ℚ, (r : ℂ) = c := by
  classical
  generalize hd : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P Q with
  | h n ih =>
    have hlim : ((P.eval (1 : ℚ) : ℚ) : ℂ) * c = ((Q.eval (1 : ℚ) : ℚ) : ℂ) := by
      have hp := ((P.continuous_eval₂ (algebraMap ℚ ℂ)).tendsto 1 |>.comp hx).mul hy
      have hq := (Q.continuous_eval₂ (algebraMap ℚ ℂ)).tendsto 1 |>.comp hx
      have hh := tendsto_nhds_unique hp (hq.congr' (hrel.mono fun _ h => h.symm))
      simpa using hh
    by_cases hp1 : P.eval 1 = 0
    · have hq1 : Q.eval 1 = 0 := by
        have hh : ((Q.eval (1 : ℚ) : ℚ) : ℂ) = 0 := by simpa [hp1] using hlim.symm
        exact_mod_cast hh
      obtain ⟨P', hpp⟩ := (Polynomial.dvd_iff_isRoot.mpr hp1)
      obtain ⟨Q', hqq⟩ := (Polynomial.dvd_iff_isRoot.mpr hq1)
      have hp' : P' ≠ 0 := by intro hz; apply hP; simp [hpp, hz]
      have hdeg : P'.natDegree < n := by
        rw [← hd, hpp, Polynomial.natDegree_mul (Polynomial.monic_X_sub_C (1 : ℚ)).ne_zero hp']
        rw [Polynomial.natDegree_X_sub_C]
        omega
      apply ih P'.natDegree hdeg P' Q' hp' ?_ rfl
      filter_upwards [hne, hrel] with t ht hr
      rw [hpp, hqq] at hr
      simp only [eval₂_mul, eval₂_sub, eval₂_X, eval₂_one, map_one] at hr
      apply mul_left_cancel₀ (sub_ne_zero.mpr ht)
      simpa only [mul_assoc] using hr
    · refine ⟨Q.eval 1 / P.eval 1, ?_⟩
      have hp1c : ((P.eval (1 : ℚ) : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hp1
      push_cast
      exact (div_eq_iff hp1c).mpr (by simpa [mul_comm] using hlim.symm)

/-- Clearing a fixed power of `1-x` preserves rationality of any finite limit. -/
theorem rational_weighted_limit_of_linear_relation {α : Type*} {l : Filter α} [NeBot l]
    {x y : α → ℂ} {c : ℂ} (d : ℕ)
    (hx : Tendsto x l (𝓝 1))
    (hy : Tendsto (fun t => (1 - x t)^d * y t) l (𝓝 c))
    (hne : ∀ᶠ t in l, x t ≠ 1)
    (P Q : ℚ[X]) (hP : P ≠ 0)
    (hrel : ∀ᶠ t in l,
      P.eval₂ (algebraMap ℚ ℂ) (x t) * y t = Q.eval₂ (algebraMap ℚ ℂ) (x t)) :
    ∃ r : ℚ, (r : ℂ) = c := by
  apply rational_limit_of_linear_relation hx hy hne P (((1 - X)^d) * Q) hP
  filter_upwards [hrel] with t ht
  simp only [eval₂_mul, eval₂_pow, eval₂_sub, eval₂_one, eval₂_X]
  calc
    _ = (1 - x t)^d * (P.eval₂ (algebraMap ℚ ℂ) (x t) * y t) := by ring
    _ = _ := by rw [ht]

end NonAlgebraicity
#print axioms NonAlgebraicity.rational_limit_of_linear_relation
#print axioms NonAlgebraicity.rational_weighted_limit_of_linear_relation
