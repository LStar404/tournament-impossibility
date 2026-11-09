import ActualMixedEvenDescent

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace RawFormalMixedSpecialization
open Matrix MixedEvenMatrix MixedCovarianceSymmetry
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

def identityInteraction : I → I → S := (1 : Matrix I I S)

def rawSource (B : Matrix I I (PowerSeries S)) : PowerSeries S :=
  PowerSeries.C (1/2:S) * ((fun _ => (1:PowerSeries S)) ⬝ᵥ
    (((B-1)*B⁻¹).mulVec (fun _ => 1)))

theorem constant_identity : constantMatrix (identityInteraction (I:=I) (S:=S))=1 := by
  apply Matrix.ext; intro i j
  simp [constantMatrix, identityInteraction, Matrix.one_apply, apply_ite]

theorem block_identity (K : I → I → S) : block K identityInteraction =
    1 + (PowerSeries.X : PowerSeries S) • constantMatrix K := by
  rw [block, constant_identity, Matrix.mul_one]

theorem inverse_source_matrix (K : I → I → S) :
    (block K identityInteraction - 1)*(block K identityInteraction)⁻¹ =
    (PowerSeries.X : PowerSeries S) • ((block K identityInteraction)⁻¹ * constantMatrix K) := by
  have hr := Matrix.mul_nonsing_inv (block K identityInteraction) (det_isUnit K identityInteraction)
  have hl := Matrix.nonsing_inv_mul (block K identityInteraction) (det_isUnit K identityInteraction)
  calc
    _ = 1 - (block K identityInteraction)⁻¹ := by rw [sub_mul, hr, one_mul]
    _ = (block K identityInteraction)⁻¹ * (block K identityInteraction - 1) := by rw [mul_sub, hl, mul_one]
    _ = _ := by rw [block_identity, add_sub_cancel_left, Matrix.mul_smul]

theorem actual_source (K : I → I → S) :
    MixedEvenCandidate.source K identityInteraction (fun _ => 1) =
      rawSource (block K identityInteraction) := by
  unfold rawSource MixedEvenCandidate.source
  rw [inverse_source_matrix, Matrix.smul_mulVec, dotProduct_smul]
  simp only [map_one, smul_eq_mul]
  ring

theorem actual_formula (K : I → I → S) (hK : ∀ i j, K i j=K j i) :
    ActualMixedEvenDescent.series K hK (fun _ => 1) identityInteraction =
      NormalizedDeterminantBranch.branch (block K identityInteraction).det *
        PowerSeries.subst (rawSource (block K identityInteraction)) (PowerSeries.exp S) := by
  have hA : ∀ i j : I, (identityInteraction (S:=S)) i j = identityInteraction j i := by
    intro i j; simp [identityInteraction, Matrix.one_apply, eq_comm]
  rw [ActualMixedEvenDescent.formula K hK identityInteraction hA, MixedEvenCandidate.candidate,
    actual_source]
  rfl

end RawFormalMixedSpecialization
#print axioms RawFormalMixedSpecialization.actual_formula
