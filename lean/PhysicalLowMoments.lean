import PhysicalWordCoefficientOrder

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PhysicalLowMoments
open PhysicalWordEvenDescent PhysicalTiltedCovariance OccurrenceWordDerivative
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem first (K A : I → I → S) (h : I → S) (i : I) :
    moment K A h [i]=mean K A h i := by simp [moment_cons,moment_nil,deletions]

theorem second (K A : I → I → S) (h : I → S) (i : I) :
    moment K A h [i,i]=(mean K A h i)^2+covariance K A i i := by
  simp [moment_cons,moment_nil,deletions]
  ring

theorem third (K A : I → I → S) (h : I → S) (i : I) :
    moment K A h [i,i,i]=(mean K A h i)^3+3*mean K A h i*covariance K A i i := by
  simp [moment_cons,moment_nil,deletions]
  ring

theorem fourth (K A : I → I → S) (h : I → S) (i : I) :
    moment K A h [i,i,i,i]=(mean K A h i)^4+6*(mean K A h i)^2*covariance K A i i+
      3*(covariance K A i i)^2 := by
  simp [moment_cons,moment_nil,deletions]
  ring

end PhysicalLowMoments
#print axioms PhysicalLowMoments.fourth
