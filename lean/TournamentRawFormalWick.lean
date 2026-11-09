import RawFormalMixedSpecialization
import BlockGaussianDeterminant

noncomputable section
attribute [local instance] Classical.typeDecidableEq
set_option maxHeartbeats 400000
namespace TournamentRawFormalWick
open BlockGaussianDeterminant RawFormalMixedSpecialization

theorem covariance_symm {n : ℕ} (T : DiamondGap.Tournament (Fin n)) (v : ℂ) :
    ∀ i j, blockQ T v i j = blockQ T v j i := by
  intro i j
  cases i <;> cases j <;> rfl

/-- Actual coefficient extraction for the original doubled tournament covariance. -/
def series {n : ℕ} (T : DiamondGap.Tournament (Fin n)) (v : ℂ) : PowerSeries ℂ :=
  ActualMixedEvenDescent.series (blockQ T v) (covariance_symm T v) (fun _ => 1) identityInteraction

/-- Formal identity only: no analytic evaluation or Condition R is asserted. -/
def formulaProof {n : ℕ} (T : DiamondGap.Tournament (Fin n)) (v : ℂ) :=
  RawFormalMixedSpecialization.actual_formula (I:=Fin n ⊕ Fin n) (S:=ℂ) (blockQ T v) (covariance_symm T v)

end TournamentRawFormalWick
#check TournamentRawFormalWick.formulaProof
#print axioms TournamentRawFormalWick.formulaProof
