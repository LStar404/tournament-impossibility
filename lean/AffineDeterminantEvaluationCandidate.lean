import WeightedSeriesEvaluation
import MixedEvenCandidate
import ActualCoreTracePrimitive
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.typeDecidableEq
set_option maxHeartbeats 800000
namespace AffineDeterminantEvaluationCandidate
open Matrix WeightedCoefficientNorm FormalSeriesDerivativeAtOne
variable {I : Type*} [Fintype I]
def affinePolynomial (Q : Matrix I I ℂ) : Matrix I I (Polynomial ℂ) :=
  (1 : Matrix I I (Polynomial ℂ))+(Polynomial.X : Polynomial ℂ) • Q.map Polynomial.C
def affineSeries (Q : Matrix I I ℂ) : Matrix I I (PowerSeries ℂ) :=
  (1 : Matrix I I (PowerSeries ℂ))+(PowerSeries.X : PowerSeries ℂ) • Q.map PowerSeries.C
lemma coe_affine (Q : Matrix I I ℂ) :
    (affinePolynomial Q).map (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)=affineSeries Q := by
  ext i j
  simp [affinePolynomial,affineSeries,Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,
    Matrix.one_apply,apply_ite]
  ring
lemma coe_det (Q : Matrix I I ℂ) :
    (((affinePolynomial Q).det:Polynomial ℂ):PowerSeries ℂ)=(affineSeries Q).det := by
  change Polynomial.coeToPowerSeries.ringHom ((affinePolynomial Q).det)=_
  rw [RingHom.map_det]
  change ((affinePolynomial Q).map (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)).det=_
  rw [coe_affine]
lemma finite_affine_det (Q : Matrix I I ℂ) {rho : ℝ} (hr : 0≤rho) :
    Finite rho (affineSeries Q).det := by
  rw [←coe_det]
  exact polynomial_finite _ hr
lemma eval_affine_det (Q : Matrix I I ℂ) (z : ℂ) :
    eval (affineSeries Q).det z=(1+z • Q).det := by
  rw [←coe_det,polynomial_eval]
  change Polynomial.evalRingHom z ((affinePolynomial Q).det)=_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [affinePolynomial,Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,apply_ite]
  ring
lemma mixed_affine (Q : Matrix I I ℂ) :
    MixedEvenMatrix.block Q RawFormalMixedSpecialization.identityInteraction=affineSeries Q := by
  have hi : MixedCovarianceSymmetry.constantMatrix
      (RawFormalMixedSpecialization.identityInteraction (I:=I) (S:=ℂ))=1 := by
    apply Matrix.ext
    intro i j
    by_cases h : i=j <;> simp [h,MixedCovarianceSymmetry.constantMatrix,RawFormalMixedSpecialization.identityInteraction,Matrix.one_apply,apply_ite]
  simp only [MixedEvenMatrix.block,hi,Matrix.mul_one,affineSeries]
  rfl
lemma eval_square_identity (Q : Matrix I I ℂ) (F : PowerSeries ℂ) {rho : ℝ}
    (hr : 0≤rho) (hF : Finite rho F) (hsquare : F^2*(affineSeries Q).det=1)
    (z : ℂ) (hz : ‖z‖≤rho) : (eval F z)^2*(1+z • Q).det=1 := by
  have hh := congrArg (fun H : PowerSeries ℂ=>eval H z) hsquare
  rw [pow_two,WeightedSeriesEvaluation.eval_mul rho (F*F) _ (finite_mul hr hF hF)
    (finite_affine_det Q hr) z hz,WeightedSeriesEvaluation.eval_mul rho F F hF hF z hz,
    eval_affine_det] at hh
  have hone : eval (1:PowerSeries ℂ) z=1 := by
    simpa using congrFun (polynomial_eval (1:Polynomial ℂ)) z
  rw [hone] at hh
  simpa only [pow_two] using hh
 theorem branch_square_eval (Q : Matrix I I ℂ) {rho : ℝ} (hr : 0≤rho)
    (hF : Finite rho (MixedEvenCandidate.branch Q RawFormalMixedSpecialization.identityInteraction))
    (z : ℂ) (hz : ‖z‖≤rho) :
    (eval (MixedEvenCandidate.branch Q RawFormalMixedSpecialization.identityInteraction) z)^2*
      (1+z • Q).det=1 := by
  apply eval_square_identity Q _ hr hF _ z hz
  have hh := NormalizedDeterminantBranch.branch_square
    (MixedEvenMatrix.block Q RawFormalMixedSpecialization.identityInteraction).det
    (MixedEvenMatrix.constant_det Q RawFormalMixedSpecialization.identityInteraction)
  simpa only [←mixed_affine,MixedEvenCandidate.branch] using hh
end AffineDeterminantEvaluationCandidate

#print axioms AffineDeterminantEvaluationCandidate.affinePolynomial
#check AffineDeterminantEvaluationCandidate.affinePolynomial

#print axioms AffineDeterminantEvaluationCandidate.affineSeries
#check AffineDeterminantEvaluationCandidate.affineSeries

#print axioms AffineDeterminantEvaluationCandidate.coe_affine
#check AffineDeterminantEvaluationCandidate.coe_affine

#print axioms AffineDeterminantEvaluationCandidate.coe_det
#check AffineDeterminantEvaluationCandidate.coe_det

#print axioms AffineDeterminantEvaluationCandidate.finite_affine_det
#check AffineDeterminantEvaluationCandidate.finite_affine_det

#print axioms AffineDeterminantEvaluationCandidate.eval_affine_det
#check AffineDeterminantEvaluationCandidate.eval_affine_det

#print axioms AffineDeterminantEvaluationCandidate.mixed_affine
#check AffineDeterminantEvaluationCandidate.mixed_affine

#print axioms AffineDeterminantEvaluationCandidate.eval_square_identity
#check AffineDeterminantEvaluationCandidate.eval_square_identity

#print axioms AffineDeterminantEvaluationCandidate.branch_square_eval
#check AffineDeterminantEvaluationCandidate.branch_square_eval
