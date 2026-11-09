import AlgebraFormalExponential
import Mathlib.RingTheory.PowerSeries.Exp

noncomputable section
namespace ZeroConstantFormalExp
variable {P : Type*} [CommRing P] [Algebra ℚ P]
def expOf (F : PowerSeries P) : PowerSeries P := (PowerSeries.exp P).subst F

theorem differential (F : PowerSeries P) (hF : F.constantCoeff=0) :
    PowerSeries.derivative (expOf F)=PowerSeries.derivative F*expOf F := by
  unfold expOf
  rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hF),
    PowerSeries.derivative_exp]
  exact mul_comm _ _

theorem constant (F : PowerSeries P) (hF : F.constantCoeff=0) : (expOf F).constantCoeff=1 := by
  unfold expOf
  change MvPowerSeries.constantCoeff _=1
  rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hF]
  simp

theorem addition (F G : PowerSeries P) (hF : F.constantCoeff=0) (hG : G.constantCoeff=0) :
    expOf (F+G)=expOf F*expOf G := by
  have hFG : (F+G).constantCoeff=0 := by simp [hF,hG]
  apply AlgebraFormalExponential.unique (S:=ℚ) (PowerSeries.derivative (F+G))
  · exact differential _ hFG
  · rw [Derivation.leibniz,differential F hF,differential G hG,map_add]
    simp only [smul_eq_mul]
    ring
  · simp only [map_mul,constant _ hF,constant _ hG,constant _ hFG,one_mul]

theorem zero : expOf (0 : PowerSeries P)=1 := by
  apply AlgebraFormalExponential.unique (S:=ℚ) 0
  · simpa using differential (0 : PowerSeries P) (by simp)
  · simp
  · simpa using constant (0 : PowerSeries P) (by simp)

theorem finite_sum {I : Type*} (s : Finset I) (F : I → PowerSeries P)
    (hF : ∀i∈s,(F i).constantCoeff=0) : expOf (∑i∈s,F i)=∏i∈s,expOf (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.prod_insert ha,addition]
    · rw [ih (fun i hi => hF i (by simp [hi]))]
    · exact hF a (by simp)
    · simp only [map_sum]
      exact Finset.sum_eq_zero (fun i hi => hF i (by simp [hi]))
end ZeroConstantFormalExp
#print axioms ZeroConstantFormalExp.finite_sum
