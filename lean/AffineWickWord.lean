import PhysicalWordCoefficientOrder

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace AffineWickWord
open OccurrenceWordDerivative OccurrenceWickPolynomial
variable {I R : Type*} [Fintype I] [CommSemiring R]

def polynomial (eta : I → R) : List I → MvPolynomial I R
  | [] => 1
  | i::w => (MvPolynomial.X i+MvPolynomial.C (eta i))*polynomial eta w

def moment (W : I → I → R) (hs : ∀i j,W i j=W j i) (eta : I → R) (w : List I) : R :=
  wick W hs (polynomial eta w)

theorem derivative (eta : I → R) (w : List I) (j : I) :
    MvPolynomial.pderiv j (polynomial eta w)=
      ((deletions w).map (fun p => if j=p.1 then polynomial eta p.2 else 0)).sum := by
  induction w with
  | nil => simp [polynomial,deletions]
  | cons i w ih =>
    simp only [polynomial,MvPolynomial.pderiv_mul,map_add,MvPolynomial.pderiv_C,add_zero,
      ih,deletions,List.map_cons,List.sum_cons,List.map_map,Function.comp_def]
    rw [MvPolynomial.pderiv_X]
    simp only [Pi.single_apply]
    rw [← List.sum_map_mul_left]
    congr 1
    · by_cases hh : j=i
      · subst j; simp
      · simp [hh,Ne.symm hh]
    · apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      split_ifs <;> simp

theorem empty (W : I → I → R) (hs : ∀i j,W i j=W j i) (eta : I → R) :
    moment W hs eta []=1 := by
  change wick W hs 1=1
  have he : MvPolynomial.monomial (0:I →₀ ℕ) (1:R)=1 := by simp
  rw [← he,wick_monomial,one_mul]
  letI : IsEmpty (Occ (0:I →₀ ℕ)) := ⟨fun x => by
    have hx : x.2.val < 0 := by simpa using x.2.isLt
    omega⟩
  exact PairingMomentParity.empty_moment_one _ _

theorem contraction_sum (f : MvPolynomial I R →+ R) (V : I → R) (eta : I → R)
    (l : List (I × List I)) :
    (∑j,V j*f ((l.map (fun p => if j=p.1 then polynomial eta p.2 else 0)).sum))=
      (l.map (fun p => V p.1*f (polynomial eta p.2))).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons,List.sum_cons,map_add,mul_add,Finset.sum_add_distrib,ih]
    congr 1
    simp only [apply_ite,map_zero,mul_ite,mul_zero]
    simp

theorem recurrence (W : I → I → R) (hs : ∀i j,W i j=W j i) (eta : I → R)
    (i : I) (w : List I) :
    moment W hs eta (i::w)=eta i*moment W hs eta w+
      ((deletions w).map (fun p => W i p.1*moment W hs eta p.2)).sum := by
  unfold moment
  rw [polynomial,add_mul,map_add,FullWickPolynomialIBP.wick_X_mul]
  have hc : wick W hs (MvPolynomial.C (eta i)*polynomial eta w)=eta i*wick W hs (polynomial eta w) := by
    rw [← MvPolynomial.smul_eq_C_mul]
    rw [map_smul,smul_eq_mul]
  rw [hc,add_comm]
  congr 1
  simp_rw [derivative]
  exact contraction_sum (wick W hs).toAddMonoidHom (W i) eta (deletions w)

end AffineWickWord
#print axioms AffineWickWord.recurrence
