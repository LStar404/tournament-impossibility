import MixedEvenMatrix

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace MixedEvenCandidate
open Matrix MixedCovarianceSymmetry MixedEvenMatrix
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

def source (K A : I → I → S) (h : I → S) : PowerSeries S :=
  PowerSeries.C (1/2:S) * PowerSeries.X *
    ((fun i => PowerSeries.C (h i)) ⬝ᵥ ((block K A)⁻¹ * constantMatrix K).mulVec (fun i => PowerSeries.C (h i)))

def branch (K A : I → I → S) := NormalizedDeterminantBranch.branch (block K A).det

def candidate (K A : I → I → S) (h : I → S) :=
  branch K A * PowerSeries.subst (source K A h) (PowerSeries.exp S)

theorem source_constant (K A : I → I → S) (h : I → S) : (source K A h).constantCoeff = 0 := by
  simp [source]

theorem expand_det (K A : I → I → S) :
    PowerSeries.expand 2 (by decide) (block K A).det = (ActualMixedWardMatrix.block K A).det := by
  change (PowerSeries.expand 2 (by decide)).toRingHom ((block K A).det) = _
  rw [RingHom.map_det]
  change ((block K A).map (PowerSeries.expand 2 (by decide)).toRingHom).det = _
  rw [expand_block]

theorem expand_source (K A : I → I → S) (h : I → S) :
    PowerSeries.expand 2 (by decide) (source K A h) = MixedSourceQuadraticDerivative.source K A h := by
  have hi := expand_inverse K A
  have he (i j : I) := congrArg (fun M => M i j) hi
  simp only [Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at he
  simp [source, MixedSourceQuadraticDerivative.source, MixedWardSolution.covariance,
    dotProduct, Matrix.mulVec, Matrix.mul_apply, constantMatrix, PowerSeries.expand_C, he]

theorem expand_subst' (f g : PowerSeries S) (hf : f.constantCoeff=0) :
    PowerSeries.expand 2 (by decide) (PowerSeries.subst f g) =
      PowerSeries.subst (PowerSeries.expand 2 (by decide) f) g := by
  exact PowerSeries.expand_subst 2 (by decide) (PowerSeries.HasSubst.of_constantCoeff_zero' hf) g

theorem expand_branch (K A : I → I → S) :
    PowerSeries.expand 2 (by decide) (branch K A) = ActualMixedDeterminantJacobi.determinantBranch K A := by
  have hz : ((block K A).det-1).constantCoeff=0 := by simp [constant_det]
  unfold branch NormalizedDeterminantBranch.branch
  rw [expand_subst' _ _ hz]
  simp only [map_sub, map_one, expand_det]
  rfl

theorem expand_candidate (K A : I → I → S) (h : I → S) :
    PowerSeries.expand 2 (by decide) (candidate K A h) = MixedDeterminantCandidateODE.candidate K A h := by
  rw [candidate, map_mul, expand_branch,
    expand_subst' _ _ (source_constant K A h), expand_source]
  rfl

end MixedEvenCandidate
#print axioms MixedEvenCandidate.expand_candidate
