import BinaryCanonicalNumbering
import ActualRecoveryDerivativeBridge

/-! Fixed positive-depth canonical
numerical tensors inherit actual untruncated recovery, a genuine outer radius,
and actual derivatives. No extremal classification is asserted. -/
noncomputable section
namespace CanonicalGraphRecovery
open BinaryCanonicalNumbering ActualGraphCoreRecovery
open PermanentNormalizedFrozenBridge RecoveryMomentTail WeightedRecoveryClosure

section Graph
variable {m : ℕ} (d : ℕ) (B : Matrix (Fin m) (Fin m) ℝ)
variable (hn : 24 ≤ m*2^(d+1))
variable (hB : ∀ i j, B j i = -B i j) (he : ∀ i j, |B i j| ≤ 1)
variable (v : ℝ) (hv : |v| ≤ 1)
include hn hB he hv

/-- Genuine radius 17/16, transported from the old 9/8 bounds for core*C_j.
No recovery-window hypothesis is needed for this convergence statement. -/
theorem outer_radius (p : ℕ) :
    let M := TournamentSkewMargin.branch (canonicalFinGraph m (d+1) B) v
    WeightedCoefficientNorm.Finite (17/16) (untruncated M p) := by
  simpa only [realGraph_eq_canonicalFinGraph] using
    (RecoveryApproximationOuterRadius.graph hn d (reversedNumbering (d+1)) B hB he
      (canonicalCoordinates m (d+1)) v hv p)

/-- Full untruncated error with every fixed k^ell coefficient weight. -/
theorem coefficient_error (p ell : ℕ) (hp : p ≤ degree d (m*2^(d+1))) :
    let M := TournamentSkewMargin.branch (canonicalFinGraph m (d+1) B) v
    Summable (coefficientError (normalized M) (untruncated M p) ell) ∧
      (∑' k, coefficientError (normalized M) (untruncated M p) ell k) ≤
        ActualWeightedUntruncatedRecovery.errorConstant d p ell/
          (m*2^(d+1) : ℝ)^(p+1) := by
  simpa only [realGraph_eq_canonicalFinGraph, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    (ActualWeightedUntruncatedRecovery.coefficient_error hn d (reversedNumbering (d+1))
      B hB he (canonicalCoordinates m (d+1)) v hv p ell hp)

/-- The same untruncated approximation has summable absolute coefficient moments. -/
theorem weighted_summable (p ell : ℕ) (hp : p ≤ degree d (m*2^(d+1))) :
    let M := TournamentSkewMargin.branch (canonicalFinGraph m (d+1) B) v
    Summable (fun k : ℕ => weight ell k*‖(untruncated M p).coeff k‖) := by
  simpa only [realGraph_eq_canonicalFinGraph] using
    (ActualWeightedUntruncatedRecovery.weighted_summable hn d (reversedNumbering (d+1))
      B hB he (canonicalCoordinates m (d+1)) v hv p ell hp)

/-- Explicit descending-factorial coefficient interface, with the same constant. -/
theorem derivative_coefficients_at_one (p ell : ℕ)
    (hp : p ≤ degree d (m*2^(d+1))) :
    let M := TournamentSkewMargin.branch (canonicalFinGraph m (d+1) B) v
    Summable (fun k => (k.descFactorial ell : ℂ)*(untruncated M p).coeff k) ∧
      ‖fallingFactorialSum (normalized M).coeff ell-
        fallingFactorialSum (fun k => (untruncated M p).coeff k) ell‖ ≤
          ActualWeightedUntruncatedRecovery.errorConstant d p ell/
            (m*2^(d+1) : ℝ)^(p+1) := by
  simpa only [realGraph_eq_canonicalFinGraph, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    (ActualWeightedUntruncatedRecovery.derivative_coefficients_at_one hn d
      (reversedNumbering (d+1)) B hB he (canonicalCoordinates m (d+1)) v hv p ell hp)

/-- Actual analytic derivatives of the same U, not a proxy function. -/
theorem approximation_at_one (p ell : ℕ) :
    let M := TournamentSkewMargin.branch (canonicalFinGraph m (d+1) B) v
    iteratedDeriv ell (FormalSeriesDerivativeAtOne.eval (untruncated M p)) 1 =
      fallingFactorialSum (fun k => (untruncated M p).coeff k) ell := by
  simpa only [realGraph_eq_canonicalFinGraph] using
    (ActualRecoveryDerivativeBridge.approximation_at_one hn d (reversedNumbering (d+1))
      B hB he (canonicalCoordinates m (d+1)) v hv p ell)

/-- Actual normalized polynomial derivative error at z=1. -/
theorem normalized_derivative_error (p ell : ℕ)
    (hp : p ≤ degree d (m*2^(d+1))) :
    let M := TournamentSkewMargin.branch (canonicalFinGraph m (d+1) B) v
    ‖iteratedDeriv ell (normalized M).eval 1-
      iteratedDeriv ell (FormalSeriesDerivativeAtOne.eval (untruncated M p)) 1‖ ≤
        ActualWeightedUntruncatedRecovery.errorConstant d p ell/
          (m*2^(d+1) : ℝ)^(p+1) := by
  simpa only [realGraph_eq_canonicalFinGraph, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    (ActualRecoveryDerivativeBridge.normalized_derivative_error hn d (reversedNumbering (d+1))
      B hB he (canonicalCoordinates m (d+1)) v hv p ell hp)

/-- Literal canonical permanent function and the same untruncated U.
The recovery window remains explicit. No core norm, score, inverse or analytic
identification is supplied by the caller. -/
theorem actual_permanent_derivative_error (p ell : ℕ)
    (hp : p ≤ degree d (m*2^(d+1))) :
    let n := m*2^(d+1)
    let M := TournamentSkewMargin.branch (canonicalFinGraph m (d+1) B) v
    ‖iteratedDeriv ell (fun z : ℂ =>
        Matrix.permanent (fun i j => 1+(n : ℂ)*z*M i j)/(n.factorial : ℂ)) 1-
      iteratedDeriv ell (FormalSeriesDerivativeAtOne.eval (untruncated M p)) 1‖ ≤
        ActualWeightedUntruncatedRecovery.errorConstant d p ell/(n : ℝ)^(p+1) := by
  simpa only [realGraph_eq_canonicalFinGraph] using
    (ActualRecoveryDerivativeBridge.actual_permanent_derivative_error hn d
      (reversedNumbering (d+1)) B hB he (canonicalCoordinates m (d+1)) v hv p ell hp)
end Graph
end CanonicalGraphRecovery

#print axioms CanonicalGraphRecovery.outer_radius
#print axioms CanonicalGraphRecovery.coefficient_error
#print axioms CanonicalGraphRecovery.weighted_summable
#print axioms CanonicalGraphRecovery.derivative_coefficients_at_one
#print axioms CanonicalGraphRecovery.approximation_at_one
#print axioms CanonicalGraphRecovery.normalized_derivative_error
#print axioms CanonicalGraphRecovery.actual_permanent_derivative_error
