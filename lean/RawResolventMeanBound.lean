import RawResolventEntryBound

noncomputable section
namespace RawResolventMeanBound
open Matrix WithLp
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem vector_bound (x : I → ℂ) {B : ℝ} (hB : 0 ≤ B) (hx : ∀i,‖x i‖ ≤ B) :
    ‖toLp 2 x‖ ≤ Real.sqrt (Fintype.card I)*B := by
  rw [EuclideanSpace.norm_eq]
  have hh : (∑i,‖x i‖^2) ≤ (Fintype.card I:ℝ)*B^2 := by
    calc
      _ ≤ ∑i:I,B^2 := Finset.sum_le_sum (fun i hi => (sq_le_sq₀ (norm_nonneg _) hB).mpr (hx i))
      _ = _ := by simp
  calc
    _ ≤ Real.sqrt ((Fintype.card I:ℝ)*B^2) := Real.sqrt_le_sqrt hh
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq hB]

theorem mean (Q R : Matrix I I ℂ) (z : ℂ) (hR : R*(1+z • Q)=1)
    (i : I) {s K U V L : ℝ} (hs : ‖z‖ ≤ s)
    (hb : ‖(Q.mulVec (fun _ => 1)) i‖ ≤ K)
    (hrow : ‖toLp 2 (fun a => Q i a)‖ ≤ U)
    (hb2 : ‖toLp 2 (Q.mulVec (fun _ => 1))‖ ≤ V)
    (hL : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) R‖ ≤ L) :
    ‖(((z • Q)*R).mulVec (fun _ => 1)) i‖ ≤ s*K+s^2*U*L*V := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hs
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hb
  have hU0 : 0 ≤ U := (norm_nonneg _).trans hrow
  have hV0 : 0 ≤ V := (norm_nonneg _).trans hb2
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
  have hc : ‖(fun a => Q i a) ⬝ᵥ R.mulVec (Q.mulVec (fun _ => 1))‖ ≤ U*L*V := by
    apply (EuclideanBilinearContraction.matrix_bilinear _ _ _).trans
    exact mul_le_mul (mul_le_mul hrow hL (norm_nonneg _) hU0) hb2 (norm_nonneg _)
      (mul_nonneg hU0 hL0)
  have he : (((z • Q)*R).mulVec (fun _ => 1)) i =
      z*((Q.mulVec (fun _ => 1)) i)-(z*z)*
        ((fun a => Q i a) ⬝ᵥ R.mulVec (Q.mulVec (fun _ => 1))) := by
    rw [RawResolventEntryBound.inverse_split _ _ hR]
    simp only [Matrix.sub_mulVec,Pi.sub_apply,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
      Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul,Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc,← Matrix.mulVec_mulVec]
    rfl
  rw [he]
  calc
    _ ≤ ‖z*((Q.mulVec (fun _ => 1)) i)‖+
        ‖(z*z)*((fun a => Q i a) ⬝ᵥ R.mulVec (Q.mulVec (fun _ => 1)))‖ := norm_sub_le _ _
    _ = ‖z‖*‖(Q.mulVec (fun _ => 1)) i‖+‖z‖^2*
        ‖(fun a => Q i a) ⬝ᵥ R.mulVec (Q.mulVec (fun _ => 1))‖ := by
      rw [norm_mul,norm_mul,norm_mul]; ring
    _ ≤ s*K+s^2*(U*L*V) := by gcongr
    _ = _ := by ring
end RawResolventMeanBound
#print axioms RawResolventMeanBound.mean
#print axioms RawResolventMeanBound.vector_bound
