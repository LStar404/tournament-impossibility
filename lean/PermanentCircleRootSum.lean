import PermanentCircleSpectralFrobenius
import Mathlib.Analysis.Real.Sqrt

/-! Actual singular-root sum estimates. Uncompiled candidate, kept outside the
    current aggregate verification until the compilation owner checks it. -/
noncomputable section
namespace PermanentSpectralFrame
open Matrix
variable {n : ℕ}

/-- Cauchy--Schwarz for the actual unordered Gram spectrum. -/
theorem singular_root_sum_le_frobenius (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, singularRoot A i) ≤ Real.sqrt (n : ℝ) *
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) (singularRoot A)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, singular_square_sum] using h

/-- An entry bound scaled by matrix size gives a dimension-independent
Frobenius bound, without any spectral hypotheses. -/
theorem frobenius_square_le_of_entry (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (B : ℝ)
    (hentry : ∀ i j, ‖A i j‖ ≤ B / (n : ℝ)) :
    (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ B ^ 2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤
        ∑ i : Fin n, ∑ j : Fin n, (B / (n : ℝ)) ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2))
    _ = B ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [hnR]
      <;> ring

/-- The actual sum of singular roots is at most B sqrt(n) under |Aij|≤B/n. -/
theorem singular_root_sum_le_of_entry (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hentry : ∀ i j, ‖A i j‖ ≤ B / (n : ℝ)) :
    (∑ i, singularRoot A i) ≤ B * Real.sqrt (n : ℝ) := by
  have hf := frobenius_square_le_of_entry hn A B hentry
  have hs : Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ B :=
    (Real.sqrt_le_left hB).mpr hf
  exact (singular_root_sum_le_frobenius A).trans (by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (n : ℝ)))

/-- Removing the exceptional singular root can only lower the sum. -/
theorem singular_root_erase_sum_le_of_entry (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hentry : ∀ i j, ‖A i j‖ ≤ B / (n : ℝ)) (i0 : Fin n) :
    (∑ i ∈ Finset.univ.erase i0, singularRoot A i) ≤ B * Real.sqrt (n : ℝ) := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun i _ _ => Real.sqrt_nonneg (eigenvalue A i))).trans
  exact singular_root_sum_le_of_entry hn A B hB hentry

end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.singular_root_sum_le_of_entry
