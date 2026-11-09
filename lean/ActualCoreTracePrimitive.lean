import PhysicalTiltedCovariance
import RawFormalMixedSpecialization
import FullJacobiDerivation
import ZeroConstantFormalExp
import FormalFirstOrderUniqueness

/-!
A formal trace primitive identifies the existing normalized determinant branch.
No analytic logarithm or diamond-free hypothesis is used.
-/
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ActualCoreTracePrimitive
open Matrix MixedCovarianceSymmetry RawFormalMixedSpecialization
variable {I : Type*} [Fintype I]

def primitive (T : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => -(T.coeff k)/(2*(k : ℂ)))

lemma primitive_constant (T : PowerSeries ℂ) : (primitive T).constantCoeff=0 := by
  simp [primitive, PowerSeries.constantCoeff_mk]

lemma primitive_derivative_X (V : PowerSeries ℂ) :
    PowerSeries.derivative (primitive (PowerSeries.X*V))=PowerSeries.C (-1/2 : ℂ)*V := by
  ext k
  have hk : (k : ℂ)+1≠0 := by exact_mod_cast (Nat.succ_ne_zero k)
  simp only [primitive, PowerSeries.coeff_derivative, PowerSeries.coeff_mk,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

def resolvent (Q : I → I → ℂ) : Matrix I I (PowerSeries ℂ) :=
  (MixedEvenMatrix.block Q identityInteraction)⁻¹ * constantMatrix Q

def covarianceTrace (Q : I → I → ℂ) : PowerSeries ℂ :=
  (PhysicalTiltedCovariance.covariance Q identityInteraction).trace

def logBranch (Q : I → I → ℂ) : PowerSeries ℂ := primitive (covarianceTrace Q)

lemma covariance_trace (Q : I → I → ℂ) :
    covarianceTrace Q=PowerSeries.X*(resolvent Q).trace := by
  unfold covarianceTrace PhysicalTiltedCovariance.covariance resolvent
  rw [Matrix.trace_smul]
  rfl

lemma log_constant (Q : I → I → ℂ) : (logBranch Q).constantCoeff=0 :=
  primitive_constant _

lemma log_derivative (Q : I → I → ℂ) :
    PowerSeries.derivative (logBranch Q)=PowerSeries.C (-1/2 : ℂ)*(resolvent Q).trace := by
  rw [logBranch, covariance_trace]
  exact primitive_derivative_X _

lemma block_derivative (Q : I → I → ℂ) :
    FullJacobiDerivation.entryDerivative PowerSeries.derivative
      (MixedEvenMatrix.block Q identityInteraction)=constantMatrix Q := by
  rw [block_identity]
  apply Matrix.ext
  intro i j
  simp [FullJacobiDerivation.entryDerivative, Matrix.add_apply, Matrix.smul_apply,
    constantMatrix, Matrix.one_apply, apply_ite, Derivation.leibniz, smul_eq_mul]

lemma determinant_derivative (Q : I → I → ℂ) :
    PowerSeries.derivative (MixedEvenMatrix.block Q identityInteraction).det=
      (MixedEvenMatrix.block Q identityInteraction).det*(resolvent Q).trace := by
  rw [FullJacobiDerivation.unit_jacobi PowerSeries.derivative _
    (MixedEvenMatrix.det_isUnit Q identityInteraction), block_derivative]
  rfl

lemma exponential_square (Q : I → I → ℂ) :
    (ZeroConstantFormalExp.expOf (logBranch Q))^2*
      (MixedEvenMatrix.block Q identityInteraction).det=1 := by
  let E := ZeroConstantFormalExp.expOf (logBranch Q)
  let d := (MixedEvenMatrix.block Q identityInteraction).det
  have hE : PowerSeries.derivative E=PowerSeries.C (-1/2 : ℂ)*(resolvent Q).trace*E := by
    dsimp only [E]
    rw [ZeroConstantFormalExp.differential _ (log_constant Q), log_derivative]
  have hd : PowerSeries.derivative d=d*(resolvent Q).trace := determinant_derivative Q
  have hzero : PowerSeries.derivative (E^2*d)=0 := by
    rw [pow_two, Derivation.leibniz, Derivation.leibniz, hE, hd]
    simp only [smul_eq_mul]
    have hc : (PowerSeries.C (-1/2 : ℂ) : PowerSeries ℂ) +
        PowerSeries.C (-1/2 : ℂ) + 1 = 0 := by
      rw [← map_add, ← map_one PowerSeries.C, ← map_add]
      norm_num
    linear_combination (E*E*(resolvent Q).trace*d)*hc
  change E^2*d=1
  apply FormalFirstOrderUniqueness.unique 0
  · simpa using hzero
  · simp
  · have hE0 : E.constantCoeff=1 := ZeroConstantFormalExp.constant _ (log_constant Q)
    have hd0 : d.constantCoeff=1 := MixedEvenMatrix.constant_det Q identityInteraction
    simp only [map_mul, map_pow, hE0, hd0, one_pow, one_mul, map_one]

/-- Pure formal unit-branch uniqueness, independent of analytic Taylor machinery. -/
lemma branch_unique (d f g : PowerSeries ℂ) (hf : f^2*d=1) (hg : g^2*d=1)
    (hf0 : f.constantCoeff=1) (hg0 : g.constantCoeff=1) : f=g := by
  have hd : d≠0 := by intro h; simp [h] at hf
  have hs : f^2=g^2 := mul_right_cancel₀ hd (hf.trans hg.symm)
  have hn : f+g≠0 := by
    intro he
    have hh := congrArg PowerSeries.constantCoeff he
    simp only [map_add, map_zero, hf0, hg0] at hh
    norm_num at hh
  have hm : (f-g)*(f+g)=0 := by
    calc
      _ = f^2-g^2 := by ring
      _ = 0 := sub_eq_zero.mpr hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hn)

/-- Identification of the pre-existing canonical branch, not a redefinition. -/
theorem branch_eq_exp (Q : I → I → ℂ) :
    MixedEvenCandidate.branch Q identityInteraction=ZeroConstantFormalExp.expOf (logBranch Q) := by
  apply branch_unique (MixedEvenMatrix.block Q identityInteraction).det
  · exact NormalizedDeterminantBranch.branch_square _ (MixedEvenMatrix.constant_det Q _)
  · exact exponential_square Q
  · exact NormalizedDeterminantBranch.branch_constant _ (MixedEvenMatrix.constant_det Q _)
  · exact ZeroConstantFormalExp.constant _ (log_constant Q)

lemma source_eq_half_mean (Q : I → I → ℂ) :
    MixedEvenCandidate.source Q identityInteraction (fun _ => 1)=
      PowerSeries.C (1/2 : ℂ)*∑ i, PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1) i := by
  unfold MixedEvenCandidate.source PhysicalTiltedCovariance.mean PhysicalTiltedCovariance.covariance
  rw [Matrix.smul_mulVec]
  simp only [map_one, Pi.smul_apply, smul_eq_mul, dotProduct, one_mul]
  rw [← Finset.mul_sum]
  ring

end ActualCoreTracePrimitive
#print axioms ActualCoreTracePrimitive.branch_eq_exp
#print axioms ActualCoreTracePrimitive.source_eq_half_mean
