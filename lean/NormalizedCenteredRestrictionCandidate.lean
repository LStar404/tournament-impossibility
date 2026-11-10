import IndependentCenteredRestrictionCandidate
import DeletionRenormalizationCandidate

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
Normalization scalar after independent restriction.
No graph entry, actual retained-set indexing, or scaling-existence claim. -/
set_option autoImplicit false
noncomputable section
namespace NormalizedCenteredRestrictionCandidate
open Matrix
open scoped Matrix.Norms.L2Operator
open IndependentCenteredRestrictionCandidate
variable {n m : ℕ}

/-- The retained enumeration covers precisely the specified complement. -/
lemma retained_sum (e : Fin m ↪ Fin n) (I : Finset (Fin n))
    (he : Finset.univ.image e = Iᶜ) (g : Fin n → ℝ) :
    (∑ i, g (e i)) = ∑ i ∈ Iᶜ, g i := by
  rw [← he, Finset.sum_image]
  intro a ha b hb hab
  exact e.injective hab

lemma retained_matrix_mass (A : Matrix (Fin n) (Fin n) ℝ)
    (e f : Fin m ↪ Fin n) (I J : Finset (Fin n))
    (he : Finset.univ.image e = Iᶜ) (hf : Finset.univ.image f = Jᶜ) :
    (∑ i, ∑ j, A (e i) (f j)) = IndependentDeletionMass.remainingMass A I J := by
  simp_rw [retained_sum f J hf]
  exact retained_sum e I he (fun i => ∑ j ∈ Jᶜ, A i j)

lemma retained_row_mass (A : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin m ↪ Fin n) (J : Finset (Fin n))
    (hf : Finset.univ.image f = Jᶜ) (i : Fin n) :
    (∑ j, A i (f j)) = 1+IndependentDeletionMass.rowResidual A i-∑ j ∈ J,A i j := by
  rw [retained_sum f J hf]
  have hh := Finset.sum_add_sum_compl J (fun j => A i j)
  unfold IndependentDeletionMass.rowResidual
  linarith

lemma retained_col_mass (A : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin m ↪ Fin n) (I : Finset (Fin n))
    (he : Finset.univ.image e = Iᶜ) (j : Fin n) :
    (∑ i, A (e i) j) = 1+IndependentDeletionMass.colResidual A j-∑ i ∈ I,A i j := by
  rw [retained_sum e I he (fun i => A i j)]
  have hh := Finset.sum_add_sum_compl I (fun i => A i j)
  unfold IndependentDeletionMass.colResidual
  linarith

/-- Finite normalized spectral bound. The scalar denominator is the actual
retained dimension plus its mass discrepancy, not the original n. -/
theorem normalized_centered_bound (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) (e f : Fin m ↪ Fin n)
    {q k K : ℝ} (hq : 0 ≤ q) (hK : |k| ≤ K) (hsmall : K < (m:ℝ))
    (hA : ‖proj n*A*proj n‖ ≤ q) :
    ‖proj m * (((n:ℝ)/((m:ℝ)+k):ℂ) • A.submatrix e f) * proj m‖ ≤
      (n:ℝ)*q/((m:ℝ)-K) := by
  have hd := DeletionRenormalizationCandidate.denominator_pos hK hsmall
  have hdK : 0 < (m:ℝ)-K := sub_pos.mpr hsmall
  have hlo : (m:ℝ)-K ≤ (m:ℝ)+k := by
    have hh := (abs_le.mp hK).1
    linarith
  have hs : 0 ≤ (n:ℝ)/((m:ℝ)+k) := div_nonneg (Nat.cast_nonneg n) hd.le
  have hb := (independent_centered_norm hm A e f).trans hA
  rw [Matrix.mul_smul, Matrix.smul_mul, norm_smul]
  have hnrm : ‖((n:ℝ)/((m:ℝ)+k):ℂ)‖ = (n:ℝ)/((m:ℝ)+k) := by
    rw [norm_div]
    simp only [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n), abs_of_pos hd]
  rw [hnrm]
  calc
    _ ≤ ((n:ℝ)/((m:ℝ)+k))*q := mul_le_mul_of_nonneg_left hb hs
    _ = ((n:ℝ)*q)/((m:ℝ)+k) := by ring
    _ ≤ ((n:ℝ)*q)/((m:ℝ)-K) :=
      div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg n) hq) hdK hlo

end NormalizedCenteredRestrictionCandidate
