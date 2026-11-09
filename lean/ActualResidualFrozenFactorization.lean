import ShiftedWickFrozenSeries
import EvenUnitResidualDescent
import ResidualInsertionConvolution
import RawFormalMixedSpecialization

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ActualResidualFrozenFactorization
open FullWickSquarefreeCompatibility ResidualInsertionConvolution
variable {n : ℕ} {S : Type*} [Field S] [CharZero S] [Algebra ℚ S]

def core (M : Matrix (Fin n) (Fin n) S) : PowerSeries S :=
  ActualMixedEvenDescent.series (block M) (block_symm M) (fun _ => 1)
    (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S))

def residualU (M : Matrix (Fin n) (Fin n) S) : PowerSeries S :=
  insertionConvolution (block M) (block_symm M) (fun _ => 1)
    (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S))
    (FactorizedResidualIdentity.actualResidual (S:=S))

def residualZ (M : Matrix (Fin n) (Fin n) S) : PowerSeries S :=
  EvenUnitResidualDescent.extract (residualU M)

theorem core_constant (M : Matrix (Fin n) (Fin n) S) : (core M).constantCoeff=1 := by
  unfold core ActualMixedEvenDescent.series
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_mk]
  rw [show 2*0=0 from rfl,PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact ActualMixedSourceTimeODE.Z_initial (block M) (block_symm M) (fun _ => 1)
    (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S))

theorem identity_symmetry : ∀i j : Fin n ⊕ Fin n,
    (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S)) i j =
    (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S)) j i := by
  intro i j; simp [RawFormalMixedSpecialization.identityInteraction,Matrix.one_apply,eq_comm]

theorem even_factorization (M : Matrix (Fin n) (Fin n) S) :
    PowerSeries.expand 2 (by decide) (FrozenSeriesGrouping.series M) =
      PowerSeries.expand 2 (by decide) (core M)*residualU M := by
  have he := actual_shifted_identity (block M) (block_symm M)
  rw [ShiftedWickFrozenSeries.shifted_identity] at he
  have hz := ActualMixedEvenDescent.expand_series (block M) (block_symm M)
    (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S)) identity_symmetry (fun _ => 1)
  change PowerSeries.expand 2 (by decide) (core M)=_ at hz
  rw [hz]
  exact he

theorem residual_reconstruction (M : Matrix (Fin n) (Fin n) S) :
    PowerSeries.expand 2 (by decide) (residualZ M)=residualU M :=
  EvenUnitResidualDescent.actual_reconstruction _ _ _ (core_constant M) (even_factorization M)

theorem residual_odd_zero (M : Matrix (Fin n) (Fin n) S) (k : ℕ) :
    (residualU M).coeff (2*k+1)=0 :=
  EvenUnitResidualDescent.odd_zero _ _ _ (core_constant M) (even_factorization M) k

theorem frozen_factorization (M : Matrix (Fin n) (Fin n) S) :
    FrozenSeriesGrouping.series M=core M*residualZ M :=
  EvenUnitResidualDescent.factorization _ _ _ (core_constant M) (even_factorization M)

theorem polynomial_factorization (M : Matrix (Fin n) (Fin n) S) :
    (FrozenPartialPairingPolynomial.frozenPolynomial M : PowerSeries S)=core M*residualZ M := by
  rw [← FrozenSeriesGrouping.series_coe]
  exact frozen_factorization M

theorem core_formula (M : Matrix (Fin n) (Fin n) S) :
    core M=MixedEvenCandidate.candidate (block M)
      (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S)) (fun _ => 1) :=
  ActualMixedEvenDescent.formula (block M) (block_symm M) _ identity_symmetry _

/-- Explicit finite coefficients of the original residual insertion convolution. -/
theorem residual_coefficient (M : Matrix (Fin n) (Fin n) S) (k : ℕ) :
    (residualZ M).coeff k =
      ∑ ab∈Finset.HasAntidiagonal.antidiagonal (2*k),
        (PolynomialTiltedRecurrence.tilted (block M) (block_symm M) (fun _ => 1)
          (RawFormalMixedSpecialization.identityInteraction (I:=Fin n ⊕ Fin n) (S:=S))
          ((FactorizedResidualIdentity.actualResidual (I:=Fin n ⊕ Fin n) (S:=S)).coeff ab.1)).coeff ab.2 := by
  simp only [residualZ,EvenUnitResidualDescent.extract,PowerSeries.coeff_mk,
    residualU,insertionConvolution]

end ActualResidualFrozenFactorization
#print axioms ActualResidualFrozenFactorization.frozen_factorization
#print axioms ActualResidualFrozenFactorization.residual_reconstruction

#print axioms ActualResidualFrozenFactorization.polynomial_factorization
