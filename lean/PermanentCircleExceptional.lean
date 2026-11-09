import PermanentCircleRankOne

/-! Selecting the exceptional singular root without imposing an ordering on
    the actual Gram spectrum. This file is an uncompiled candidate. -/
noncomputable section
namespace PermanentSpectralFrame
open Matrix

/-- A rank-one perturbation has at most one singular root exceeding the
operator bound for the remainder. The exceptional coordinate exists also
when no root exceeds that bound. -/
theorem exists_exceptional_root {n : ℕ} (hn : 0 < n)
    (u w : Fin n → ℂ) (E : Matrix (Fin n) (Fin n) ℂ)
    (q : ℝ) (hq : 0 ≤ q)
    (hE : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) E‖ ≤ q) :
    ∃ i0 : Fin n, ∀ i : Fin n, i ≠ i0 →
      singularRoot (rankOne u w + E) i ≤ q := by
  classical
  by_cases hbad : ∃ i : Fin n, q ^ 2 < eigenvalue (rankOne u w + E) i
  · obtain ⟨i0, hi0⟩ := hbad
    refine ⟨i0, ?_⟩
    intro i hne
    have hi : eigenvalue (rankOne u w + E) i ≤ q ^ 2 := by
      by_contra h
      exact hne (bad_indices_equal u w E q hq hE i i0 (lt_of_not_ge h) hi0)
    exact (Real.sqrt_le_left hq).mpr hi
  · refine ⟨⟨0, hn⟩, ?_⟩
    intro i _
    have hi : eigenvalue (rankOne u w + E) i ≤ q ^ 2 := by
      by_contra h
      exact hbad ⟨i, lt_of_not_ge h⟩
    exact (Real.sqrt_le_left hq).mpr hi

end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.exists_exceptional_root
