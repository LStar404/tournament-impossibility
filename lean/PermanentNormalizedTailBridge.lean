import PermanentNormalizedFrozenBridge
import BinaryGraphPermanentTail

/-! The normalized polynomial used by the exact rho-Fk identity is the same
actual polynomial controlled by the proved permanent tail bound. -/
noncomputable section
namespace PermanentNormalizedTailBridge
open PermanentNormalizedFrozenBridge PermanentPolynomialCircleTail PermanentSpectralFrame
open BinaryBalancedTensor BinaryRawGraphWeighted

lemma scalar_nonzero {n : ℕ} (hn : 0 < n) :
    (n : ℂ)^n/(n.factorial : ℂ) ≠ 0 := by
  exact div_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

theorem support_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    (normalized M).support = (permanentPolynomial (averaging n) M).support := by
  classical
  ext k
  simp only [Polynomial.mem_support_iff, normalized, Polynomial.coeff_C_mul]
  constructor
  · intro h
    exact (mul_ne_zero_iff.mp h).2
  · intro h
    exact mul_ne_zero (scalar_nonzero hn) h

theorem coefficient_norm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (k : ℕ) :
    ‖(normalized M).coeff k‖ = ‖(permanentPolynomial (averaging n) M).coeff k‖ /
      ((n.factorial : ℝ)/(n : ℝ)^n) := by
  rw [normalized, Polynomial.coeff_C_mul, norm_mul, norm_div, norm_pow,
    Complex.norm_natCast, Complex.norm_natCast]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hf0 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

theorem empty_matrix (M : Matrix (Fin 0) (Fin 0) ℂ) : normalized M = 1 := by
  have hp : permanentPolynomial (averaging 0) M = 1 := by
    unfold permanentPolynomial
    exact Matrix.permanent_isEmpty
  rw [normalized, hp]
  norm_num

theorem eval_actual {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (z : ℂ) :
    (normalized M).eval z =
      Matrix.permanent (fun i j => 1+(n : ℂ)*z*M i j)/(n.factorial : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have he : (fun i j => 1+(n : ℂ)*z*M i j) =
      (n : ℂ) • (averaging n + z • M) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, averaging, smul_eq_mul]
    field_simp
  rw [he, Matrix.permanent_smul]
  simp only [normalized, Polynomial.eval_mul, Polynomial.eval_C,
    permanentPolynomial_eval, Fintype.card_fin]
  ring

/-- Genuine high-degree tail of exactly the normalized polynomial whose
coefficients were identified with rho*Fk, at every fixed inverse-power order. -/
theorem graph_tail {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (hn : 24 ≤ n) (r : ℕ)
    (e : Bits (r+1) ≃ Fin (2^(r+1))) (B : Matrix C C ℝ)
    (hB : ∀ i j, B j i = -B i j) (he : ∀ i j, |B i j| ≤ 1)
    (f : Fin n ≃ C × Bits (r+1)) (v : ℝ) (hv : |v| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (p : ℕ) :
    let M := TournamentSkewMargin.branch (realGraph (r+1) e B f) v
    (∑ k ∈ (normalized M).support.filter (fun k => ⌊δ*(n : ℝ)⌋₊ < k),
      ‖(normalized M).coeff k‖) ≤
      PermanentActualCircleTail.tailConstant ((2 : ℝ)^(r+1)+1) 1 (5/4) (3/4) δ p /
        (n : ℝ)^p := by
  dsimp only
  have hn0 : 0 < n := by omega
  rw [support_eq _ hn0]
  simp_rw [coefficient_norm _ hn0]
  rw [← Finset.sum_div]
  exact BinaryGraphPermanentTail.normalized_tail hn r e B hB he f v hv hδ p

end PermanentNormalizedTailBridge

#print axioms PermanentNormalizedTailBridge.eval_actual
#print axioms PermanentNormalizedTailBridge.graph_tail
