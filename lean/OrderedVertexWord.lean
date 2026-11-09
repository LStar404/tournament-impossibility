import GlobalLogDegreeAssignments
import ResidualPhysicalAssignments
import PhysicalPartialMatching
import PhysicalActivityOrder

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace OrderedVertexWord
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def word {b : ℕ} (d : Fin b →₀ ℕ) (a : Fin b → I) : List I :=
  (ResidualDegreeAssignments.word d).map a

theorem length {b : ℕ} (d : Fin b →₀ ℕ) (a : Fin b → I) :
    (word d a).length=∑v,d v := by
  simp only [word,List.length_map,ResidualDegreeAssignments.length_word]

theorem product {R : Type*} [CommMonoid R] {b : ℕ}
    (d : Fin b →₀ ℕ) (a : Fin b → I) (f : I → R) :
    ((word d a).map f).prod=∏v,f (a v)^(d v) := by
  have hh (l : List (Fin b)) :
      ((l.flatMap (fun v => List.replicate (d v) (a v))).map f).prod=
        (l.map (fun v => f (a v)^(d v))).prod := by
    induction l with
    | nil => simp
    | cons v l ih => simp [ih]
  simpa only [word,ResidualDegreeAssignments.word,List.map_flatMap,List.map_replicate,
    Finset.prod_map_toList] using hh Finset.univ.toList


theorem polynomial {b : ℕ} (d : Fin b →₀ ℕ) (a : Fin b → I) :
    OccurrenceWordDerivative.polynomial (S:=S) (word d a)=∏v,(MvPolynomial.X (a v))^(d v) := by
  have hh (w : List I) : OccurrenceWordDerivative.polynomial (S:=S) w=
      (w.map (fun i => (MvPolynomial.X i : MvPolynomial I S))).prod := by
    induction w with
    | nil => rfl
    | cons i w ih => simp [OccurrenceWordDerivative.polynomial,ih]
  rw [hh,product]

theorem affine_polynomial {R : Type*} [CommSemiring R] {b : ℕ}
    (eta : I → R) (d : Fin b →₀ ℕ) (a : Fin b → I) :
    AffineWickWord.polynomial eta (word d a)=
      ∏x : StructuralPartialMatchingCounts.Positions d,
        (MvPolynomial.X (a x.1)+MvPolynomial.C (eta (a x.1))) := by
  have hh (w : List I) : AffineWickWord.polynomial eta w=
      (w.map (fun i => MvPolynomial.X i+MvPolynomial.C (eta i))).prod := by
    induction w with
    | nil => rfl
    | cons i w ih => simp [AffineWickWord.polynomial,ih]
  rw [hh,product,Fintype.prod_sigma]
  simp

theorem physical_matching {b : ℕ} (K A : I → I → S)
    (hK : ∀i j,K i j=K j i) (hA : ∀i j,A i j=A j i) (h : I → S)
    (d : Fin b →₀ ℕ) (a : Fin b → I) :
    PhysicalWordEvenDescent.moment K A h (word d a)=
      PartialMatchingAffine.total (PhysicalTiltedCovariance.covariance K A)
        (PhysicalPartialMatching.covariance_symmetry K A hK hA)
        (PhysicalTiltedCovariance.mean K A h) (fun x : StructuralPartialMatchingCounts.Positions d => a x.1) := by
  rw [← PhysicalPartialMatching.affine_eq_physical K A hK hA h]
  unfold AffineWickWord.moment
  rw [affine_polynomial]
  exact PartialMatchingAffine.affine_identity _ _ _ _
end OrderedVertexWord
#print axioms OrderedVertexWord.physical_matching
