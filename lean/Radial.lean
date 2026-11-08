import Mathlib.Topology.Algebra.Polynomial
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Complex.Basic

/-!
The polynomial part of Appendix A.3.  The outer variable is the radial
coordinate, and the inner variable is the finite function value.  A relation
may vanish identically at the endpoint; root multiplicity removes exactly
that obstruction before taking the limit.
-/

open Polynomial Filter Topology
namespace NonAlgebraicity

abbrev BiPoly := Polynomial (Polynomial ℚ)

noncomputable def evalXY (p : BiPoly) (x y : ℂ) : ℂ :=
  p.eval₂ (Polynomial.eval₂RingHom (algebraMap ℚ ℂ) y) x

theorem tendsto_evalXY {α : Type*} {l : Filter α} {x y : α → ℂ}
    {a b : ℂ} (hx : Tendsto x l (𝓝 a)) (hy : Tendsto y l (𝓝 b)) (p : BiPoly) :
    Tendsto (fun t => evalXY p (x t) (y t)) l (𝓝 (evalXY p a b)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [evalXY, Polynomial.eval₂_add] using hp.add hq
  | monomial n q =>
      simpa only [evalXY, Polynomial.eval₂_monomial, Polynomial.coe_eval₂RingHom,
        Function.comp_apply] using
        ((q.continuous_eval₂ (algebraMap ℚ ℂ)).tendsto b |>.comp hy).mul (hx.pow n)

/-- A finite limit of a branch satisfying a nonzero rational polynomial
relation is algebraic. This includes the removal of common endpoint factors;
no nonvanishing-specialization hypothesis is assumed. -/
theorem algebraic_limit_of_relation {α : Type*} {l : Filter α} [NeBot l]
    {x y : α → ℂ} {c : ℂ}
    (hx : Tendsto x l (𝓝 1)) (hy : Tendsto y l (𝓝 c))
    (hne : ∀ᶠ t in l, x t ≠ 1)
    (p : BiPoly) (hp : p ≠ 0)
    (hrel : ∀ᶠ t in l, evalXY p (x t) (y t) = 0) : IsAlgebraic ℚ c := by
  obtain ⟨q, hpq, hndvd⟩ :=
    p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp (1 : Polynomial ℚ)
  have hq : q.eval 1 ≠ 0 := by
    intro h
    apply hndvd
    exact Polynomial.dvd_iff_isRoot.mpr h
  have hzero : ∀ᶠ t in l, evalXY q (x t) (y t) = 0 := by
    filter_upwards [hne, hrel] with t ht hrt
    rw [hpq] at hrt
    simp only [evalXY, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_one, map_one] at hrt
    exact (mul_eq_zero.mp hrt).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr ht))
  have hend : evalXY q 1 c = 0 :=
    tendsto_nhds_unique (tendsto_evalXY hx hy q)
      (tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm))
  refine ⟨q.eval 1, hq, ?_⟩
  simpa only [evalXY, Polynomial.eval₂_at_one, Polynomial.coe_eval₂RingHom,
    Polynomial.aeval_def] using hend

/-- Contrapositive used for the normalized generating functions. -/
theorem no_relation_of_transcendental_limit {α : Type*} {l : Filter α} [NeBot l]
    {x y : α → ℂ} {c : ℂ}
    (hx : Tendsto x l (𝓝 1)) (hy : Tendsto y l (𝓝 c))
    (hne : ∀ᶠ t in l, x t ≠ 1) (hc : Transcendental ℚ c) :
    ¬ ∃ p : BiPoly, p ≠ 0 ∧ ∀ᶠ t in l, evalXY p (x t) (y t) = 0 := by
  rintro ⟨p, hp, hrel⟩
  exact hc (algebraic_limit_of_relation hx hy hne p hp hrel)

#print axioms algebraic_limit_of_relation
#print axioms no_relation_of_transcendental_limit

end NonAlgebraicity
