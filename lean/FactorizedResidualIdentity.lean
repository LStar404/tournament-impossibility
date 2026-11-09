import AlgebraFormalExponential

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace FactorizedResidualIdentity
open FormalDividedPowers FormalMixedExponential AlgebraFormalExponential
variable {S P : Type*} [Field S] [CharZero S] [CommRing P] [Algebra S P]

def localCore (a : P) := mixed (S:=S) a ((-1/2:S) • a^2)
def residual (a : P) := (1+PowerSeries.C a*PowerSeries.X)*mixed (S:=S) (-a) ((1/2:S) • a^2)

theorem local_factorization (a : P) :
    localCore (S:=S) a * residual (S:=S) a=1+PowerSeries.C a*PowerSeries.X := by
  have hh : (1/2:S) • a^2 = -((-1/2:S) • a^2) := by simp [neg_div]
  unfold localCore residual
  rw [hh]
  calc
    _ = (1+PowerSeries.C a*PowerSeries.X) *
        (mixed (S:=S) a ((-1/2:S) • a^2)*mixed (S:=S) (-a) (-((-1/2:S) • a^2))) := by ring
    _ = _ := by rw [mixed_opposite,mul_one]

theorem finite_factorization {I : Type*} (s : Finset I) (a : I → P) :
    mixed (S:=S) (∑i∈s,a i) ((-1/2:S) • ∑i∈s,(a i)^2) *
      (∏i∈s,residual (S:=S) (a i)) = ∏i∈s,(1+PowerSeries.C (a i)*PowerSeries.X) := by
  rw [Finset.smul_sum,mixed_sum,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact local_factorization (a i)

variable {I : Type*} [Fintype I]

def actualResidual : PowerSeries (MvPolynomial I S) :=
  ∏i : I,residual (S:=S) (MvPolynomial.X i)

def shiftedProduct : PowerSeries (MvPolynomial I S) :=
  ∏i : I,(1+PowerSeries.C (MvPolynomial.X i)*PowerSeries.X)

theorem actual_core : ActualMixedSourceWard.E (fun _ : I => (1:S)) (1 : Matrix I I S) =
    mixed (S:=S) (∑i : I,MvPolynomial.X i) ((-1/2:S) • ∑i : I,(MvPolynomial.X i)^2) := by
  simp [ActualMixedSourceWard.E,LinearSourceExpansion.source,MixedSourcePolynomials.interaction,
    Matrix.one_apply,pow_two]

theorem actual_factorization :
    ActualMixedSourceWard.E (fun _ : I => (1:S)) (1 : Matrix I I S)*actualResidual (I:=I) (S:=S)=
      shiftedProduct (I:=I) (S:=S) := by
  rw [actual_core]
  exact finite_factorization Finset.univ (fun i : I => (MvPolynomial.X i : MvPolynomial I S))

end FactorizedResidualIdentity
#print axioms FactorizedResidualIdentity.actual_factorization
