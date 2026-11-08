import Radial
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.ScaleRoots

open Polynomial Filter Topology
namespace NonAlgebraicity

theorem evalXY_eq_aevalAeval (p : BiPoly) (x y : ℂ) :
    evalXY p x y = Polynomial.aevalAeval y x p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [evalXY, map_add] using congrArg₂ (· + ·) hp hq
  | monomial n q =>
      simp [evalXY, ← Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.coe_eval₂RingHom, Polynomial.aeval_def]

theorem evalXY_swap (p : BiPoly) (x y : ℂ) :
    evalXY (Polynomial.Bivariate.swap p) x y = evalXY p y x := by
  simp only [evalXY_eq_aevalAeval, Polynomial.Bivariate.aevalAeval_swap]

/-- Clear the denominators in P(x, Y/(1-x)^d).  Swapping variables lets
mathlib's scaleRoots operate in the function-value variable. -/
noncomputable def normalizeRelation (p : BiPoly) (d : ℕ) : BiPoly :=
  Polynomial.Bivariate.swap
    ((Polynomial.Bivariate.swap p).scaleRoots ((1 - Polynomial.X) ^ d))

theorem normalizeRelation_ne_zero {p : BiPoly} (hp : p ≠ 0) (d : ℕ) :
    normalizeRelation p d ≠ 0 := by
  apply (map_ne_zero_iff (Polynomial.Bivariate.swap) Polynomial.Bivariate.swap.injective).mpr
  apply Polynomial.scaleRoots_ne_zero
  exact (map_ne_zero_iff (Polynomial.Bivariate.swap) Polynomial.Bivariate.swap.injective).mpr hp

theorem normalizeRelation_vanishes {p : BiPoly} {x y : ℂ} (d : ℕ)
    (h : evalXY p x y = 0) :
    evalXY (normalizeRelation p d) x ((1 - x) ^ d * y) = 0 := by
  rw [normalizeRelation, evalXY_swap]
  have hp : evalXY (Polynomial.Bivariate.swap p) y x = 0 := by
    rwa [evalXY_swap]
  have ht := Polynomial.scaleRoots_eval₂_eq_zero
    (s := (1 - Polynomial.X) ^ d)
    (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) x) hp
  simpa [evalXY, Polynomial.coe_eval₂RingHom] using ht

/-- Appendix A.3 after rational descent: any finite radial limit of a
polynomially normalized algebraic branch is algebraic. -/
theorem algebraic_weighted_limit_of_relation {α : Type*} {l : Filter α} [NeBot l]
    {x y : α → ℂ} {c : ℂ} (d : ℕ)
    (hx : Tendsto x l (𝓝 1))
    (hy : Tendsto (fun t => (1 - x t) ^ d * y t) l (𝓝 c))
    (hne : ∀ᶠ t in l, x t ≠ 1)
    (p : BiPoly) (hp : p ≠ 0)
    (hrel : ∀ᶠ t in l, evalXY p (x t) (y t) = 0) : IsAlgebraic ℚ c := by
  apply algebraic_limit_of_relation hx hy hne (normalizeRelation p d)
    (normalizeRelation_ne_zero hp d)
  exact hrel.mono fun _ h => normalizeRelation_vanishes d h

#print axioms algebraic_weighted_limit_of_relation
end NonAlgebraicity
