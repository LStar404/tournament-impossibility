import QRegularGeometricLimit
import Lean

/-! Application checks only: not an exported project root or certificate module.
The main endpoint below takes geometric convergence alone, with no full-sequence
limit, FourExponentialIndependence, or Lindemann–Weierstrass premise. -/
open Filter Topology
open NonAlgebraicity
open Lean Elab Command Meta

#check (qRegular_geometric_limit_rational :
  ∀ (q : ℕ), 2 ≤ q → ∀ (a : ℕ → ℚ) (d : ℕ) (L : ℂ),
    IsQRegular q (fun n => (a n : ℂ)) →
    Tendsto (fun e : ℕ =>
      (q : ℂ) ^ (-((d * e : ℕ) : ℤ)) * (a (q ^ e) : ℂ)) atTop (𝓝 L) →
    ∃ r : ℚ, (r : ℂ) = L)

example (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℚ) (d : ℕ) (L : ℂ)
    (ha : IsQRegular q (fun n => (a n : ℂ)))
    (hlim : Tendsto (fun e : ℕ =>
      (q : ℂ) ^ (-((d * e : ℕ) : ℤ)) * (a (q ^ e) : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L :=
  qRegular_geometric_limit_rational q hq a d L ha hlim

example (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℚ) (L : ℂ)
    (ha : IsQRegular q (fun n => (a n : ℂ)))
    (hlim : Tendsto (fun e : ℕ => (a (q ^ e) : ℂ)) atTop (𝓝 L)) :
    ∃ r : ℚ, (r : ℂ) = L :=
  qRegular_geometric_limit_rational q hq a 0 L ha (by simpa using hlim)

example (q : ℕ) (hq : 2 ≤ q) (e : ℕ) : 0 < q ^ e :=
  pow_pos (by omega) _
example (q : ℕ) : q ^ (0 : ℕ) = 1 := by simp
example (q e : ℕ) (a : ℕ → ℚ) :
    (q : ℂ) ^ (-((0 * e : ℕ) : ℤ)) * (a (q ^ e) : ℂ) = (a (q ^ e) : ℂ) := by simp
example (a : ℕ → ℚ) : ((a 0 / (0 : ℚ)^0 : ℚ) : ℂ) = (a 0 : ℂ) := by simp
example (a : ℕ → ℚ) (d : ℕ) (hd : 0 < d) :
    ((a 0 / (0 : ℚ)^d : ℚ) : ℂ) = 0 := by
  simp [zero_pow (Nat.ne_of_gt hd)]

run_cmd do
  let env := (← getEnv).setExporting false
  let some old := env.find? ``NonAlgebraicity.qRegular_scaled_limit_rational
    | throwError "Original full-sequence endpoint is missing"
  let some new := env.find? ``NonAlgebraicity.qRegular_scaled_limit_rational_from_geometric
    | throwError "New full-sequence corollary is missing"
  liftTermElabM do
    unless ← isDefEq old.type new.type do
      throwError "Full-sequence corollary type differs from original endpoint"
  logInfo "COROLLARY_TYPE_DEFINITIONALLY_EQUAL"
  logInfo "GEOMETRIC_APPLICATION_CHECKS_PASSED"
