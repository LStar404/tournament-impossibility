import OrderedResidualPolynomial

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace OrderedResidualTilted
open OrderedResidualPolynomial PhysicalWordRecurrence PolynomialTiltedRecurrence
variable {I S : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]

def momentCoefficient (K A : I → I → S) (h : I → S) (m : ℕ) : PowerSeries S :=
  ∑b∈Finset.range (m/3+1),∑a : Fin b → I,
    ∑d∈Finset.finsuppAntidiag (Finset.univ : Finset (Fin b)) m,
      PowerSeries.C (scalar (S:=S) d)*
        PhysicalWordEvenDescent.moment K A h (OrderedVertexWord.word d a)

theorem shifted_insertion (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (h : I → S) (m : ℕ) :
    PowerSeries.X^m*tilted K hK h A ((FactorizedResidualIdentity.actualResidual (I:=I) (S:=S)).coeff m)=
      ∑b∈Finset.range (m/3+1),∑a : Fin b → I,
        ∑d∈Finset.finsuppAntidiag (Finset.univ : Finset (Fin b)) m,
          PowerSeries.C (scalar (S:=S) d)*physical K hK h A (OrderedVertexWord.word d a) := by
  rw [coefficient]
  change PowerSeries.X^m*(tiltedAdd K hK h A) _ = _
  simp only [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  change PowerSeries.X^m*tilted K hK h A _ = _
  rw [ResidualPhysicalAssignments.tilted_smul,physical,OrderedVertexWord.length,
    (Finset.mem_finsuppAntidiag.mp hd).1]
  ring

theorem expansion (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (m : ℕ) :
    PowerSeries.expand 2 (by decide) (momentCoefficient K A h m)=
      PowerSeries.X^m*tilted K hK h A ((FactorizedResidualIdentity.actualResidual (I:=I) (S:=S)).coeff m) := by
  rw [momentCoefficient,shifted_insertion]
  simp only [map_sum,map_mul,PowerSeries.expand_C,
    PhysicalWordEvenDescent.expand_moment K hK h A hA]

theorem eq_old (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (m : ℕ) :
    momentCoefficient K A h m=ResidualPhysicalAssignments.momentCoefficient K A h m := by
  ext k
  have hh : PowerSeries.expand 2 (by decide) (momentCoefficient K A h m)=
      PowerSeries.expand 2 (by decide) (ResidualPhysicalAssignments.momentCoefficient K A h m) := by
    rw [expansion K A hK hA,ResidualPhysicalAssignments.expansion K hK h A hA]
  have hc := congrArg (fun F : PowerSeries S => F.coeff (2*k)) hh
  simpa only [PowerSeries.coeff_expand_mul] using hc
end OrderedResidualTilted
#print axioms OrderedResidualTilted.eq_old
