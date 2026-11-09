import EuclideanBilinearContraction

noncomputable section
namespace RawResolventEntryBound
open Matrix WithLp
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem inverse_split (A R : Matrix I I ℂ) (hR : R*(1+A)=1) :
    A*R=A-A*R*A := by
  apply eq_sub_iff_add_eq.mpr
  have hh := congrArg (fun X : Matrix I I ℂ => A*X) hR
  simpa only [mul_add,mul_one,mul_assoc] using hh

theorem entry (Q R : Matrix I I ℂ) (z : ℂ) (hR : R*(1+z • Q)=1)
    (i j : I) {s C U L : ℝ} (hs : ‖z‖ ≤ s) (hC : ‖Q i j‖ ≤ C)
    (hrow : ‖toLp 2 (fun a => Q i a)‖ ≤ U) (hcol : ‖toLp 2 (fun a => Q a j)‖ ≤ U)
    (hL : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) R‖ ≤ L) :
    ‖((z • Q)*R) i j‖ ≤ s*C+s^2*U^2*L := by
  have hs0 : 0 ≤ s := (norm_nonneg z).trans hs
  have hU0 : 0 ≤ U := (norm_nonneg _).trans hrow
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  have hp : ‖(Q*R*Q) i j‖ ≤ U^2*L := by
    apply (EuclideanBilinearContraction.matrix_entry Q R i j).trans
    calc
      _  ≤  U*L*U := mul_le_mul (mul_le_mul hrow hL (norm_nonneg _) hU0) hcol
        (norm_nonneg _) (mul_nonneg hU0 hL0)
      _ = _ := by ring
  rw [inverse_split _ _ hR]
  simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    smul_eq_mul]
  calc
    _  ≤  ‖z*Q i j‖+‖(z*z)*(Q*R*Q) i j‖ := norm_sub_le _ _
    _ = ‖z‖*‖Q i j‖+‖z‖^2*‖(Q*R*Q) i j‖ := by rw [norm_mul,norm_mul,norm_mul]; ring
    _  ≤  s*C+s^2*(U^2*L) := by gcongr
    _ = _ := by ring
end RawResolventEntryBound
#print axioms RawResolventEntryBound.entry
