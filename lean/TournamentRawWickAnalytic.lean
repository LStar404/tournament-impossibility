import RawSourceTaylorBridge
import TaylorDerivativeExponential
import ActualGaussianTaylorBranch
import TournamentRawFormalWick

noncomputable section
attribute [local instance] Classical.typeDecidableEq
set_option maxHeartbeats 800000
namespace TournamentRawWickAnalytic
open BlockGaussianDeterminant GaussianScalarFactor AnalyticTaylorArithmetic
open AffineMatrixTaylorBridge

theorem formal_identity {I : Type*} [Fintype I] (Q : Matrix I I ℂ) :
    formal Q=MixedEvenMatrix.block Q RawFormalMixedSpecialization.identityInteraction := by
  erw [RawFormalMixedSpecialization.block_identity]
  rfl

theorem formal_formula {I : Type*} [Fintype I] (Q : I → I → ℂ)
    (hQ : ∀ i j, Q i j=Q j i) :
    NormalizedDeterminantBranch.branch (MixedEvenMatrix.block Q RawFormalMixedSpecialization.identityInteraction).det *
      PowerSeries.subst (RawFormalMixedSpecialization.rawSource (MixedEvenMatrix.block Q RawFormalMixedSpecialization.identityInteraction)) (PowerSeries.exp ℂ) =
        ActualMixedEvenDescent.series Q hQ (fun _ => 1) RawFormalMixedSpecialization.identityInteraction :=
  (RawFormalMixedSpecialization.actual_formula Q hQ).symm

def product {n : ℕ} (T : DiamondGap.Tournament (Fin n)) (v z : ℂ) :=
  gaussian n z*Complex.exp (RawSourceTaylorBridge.source (blockQ T v) z)

theorem analytic_product {n : ℕ} (T : DiamondGap.Tournament (Fin n)) (v : ℂ) :
    AnalyticAt ℂ (product T v) 0 :=
  (ActualGaussianTaylorBranch.gaussian_analytic n).mul (RawSourceTaylorBridge.analytic_source (blockQ T v)).cexp'

theorem generic_taylor {I : Type*} [Fintype I] (Q : I → I → ℂ)
    (hQ : ∀ i j, Q i j=Q j i) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (hb : series g=NormalizedDeterminantBranch.branch (formal Q).det) :
    series (fun z => g z*Complex.exp (RawSourceTaylorBridge.source Q z)) =
      ActualMixedEvenDescent.series Q hQ (fun _ => 1) RawFormalMixedSpecialization.identityInteraction := by
  erw [mul hg (RawSourceTaylorBridge.analytic_source Q).cexp',hb,
    TaylorDerivativeExponential.exp_series _ (RawSourceTaylorBridge.analytic_source _) (RawSourceTaylorBridge.source_zero _),
    RawSourceTaylorBridge.source_series,formal_identity]
  exact formal_formula Q hQ

theorem generic_hasSeries {I : Type*} [Fintype I] (Q : I → I → ℂ)
    (hQ : ∀ i j, Q i j=Q j i) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (hb : series g=NormalizedDeterminantBranch.branch (formal Q).det) :
    HasFPowerSeriesAt (fun z => g z*Complex.exp (RawSourceTaylorBridge.source Q z))
      (FormalMultilinearSeries.ofScalars ℂ (fun k => (ActualMixedEvenDescent.series Q hQ (fun _ => 1)
        RawFormalMixedSpecialization.identityInteraction).coeff k)) 0 := by
  rw [← generic_taylor Q hQ g hg hb]
  exact AnalyticTaylorArithmetic.hasSeries (hg.mul (RawSourceTaylorBridge.analytic_source Q).cexp')

theorem formal_decidable {I : Type*} [Fintype I] (d : DecidableEq I) (Q : Matrix I I ℂ) :
    @formal I d Q = formal Q := by
  have hd : d=Classical.typeDecidableEq I := Subsingleton.elim _ _
  cases hd
  rfl

theorem compatible_branch {n : ℕ} (T : DiamondGap.Tournament (Fin n))
    (hT : T.diamonds.card=0) (v : ℂ) (hv : v^2=1) :
    series (gaussian n)=NormalizedDeterminantBranch.branch (formal (blockQ T v)).det := by
  have hb := ActualGaussianTaylorBranch.actual_branch T hT v hv
  rw [formal_decidable] at hb
  exact hb

theorem generic_hasSeries_with {I : Type*} [Fintype I] (d : DecidableEq I)
    (Q : I → I → ℂ) (hQ : ∀ i j, Q i j=Q j i) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (hb : letI : DecidableEq I := d
          series g=NormalizedDeterminantBranch.branch (formal Q).det) :
    HasFPowerSeriesAt (fun z => g z*Complex.exp (RawSourceTaylorBridge.source Q z))
      (FormalMultilinearSeries.ofScalars ℂ (fun k => (ActualMixedEvenDescent.series Q hQ (fun _ => 1)
        RawFormalMixedSpecialization.identityInteraction).coeff k)) 0 := by
  have hd : d=Classical.typeDecidableEq I := Subsingleton.elim _ _
  subst d
  exact generic_hasSeries Q hQ g hg hb

/-- Inferred type preserves the existing actual Wick coefficient sequence. -/
def hasSeries {n : ℕ} (T : DiamondGap.Tournament (Fin n))
    (hT : T.diamonds.card=0) (v : ℂ) (hv : v^2=1) :=
  generic_hasSeries_with (inferInstance : DecidableEq (Fin n ⊕ Fin n))
    (blockQ T v) (TournamentRawFormalWick.covariance_symm T v)
    (gaussian n) (ActualGaussianTaylorBranch.gaussian_analytic n)
      (ActualGaussianTaylorBranch.actual_branch T hT v hv)

end TournamentRawWickAnalytic
#check TournamentRawWickAnalytic.hasSeries
#print axioms TournamentRawWickAnalytic.hasSeries
