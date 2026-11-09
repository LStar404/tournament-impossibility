import OccurrenceWickPolynomial
import SquarefreePairingContraction

noncomputable section
namespace OccurrenceSquarefreeEquiv
open SquarefreePairingContraction OccurrenceWickPolynomial

def equivalence {n : ℕ} (I J : Finset (Fin n)) : Occ (exponent I J) ≃ I ⊕ J where
  toFun x := match x with
    | ⟨Sum.inl i,k⟩ => Sum.inl ⟨i,by
        have h := k.isLt
        simp only [exponent_left] at h
        split_ifs at h with hi
        · exact hi
        · omega⟩
    | ⟨Sum.inr j,k⟩ => Sum.inr ⟨j,by
        have h := k.isLt
        simp only [exponent_right] at h
        split_ifs at h with hj
        · exact hj
        · omega⟩
  invFun x := match x with
    | Sum.inl i => ⟨Sum.inl i.val,⟨0,by simp [exponent_left,i.property]⟩⟩
    | Sum.inr j => ⟨Sum.inr j.val,⟨0,by simp [exponent_right,j.property]⟩⟩
  left_inv x := by
    rcases x with ⟨i,k⟩
    cases i with
    | inl i =>
      have h := k.isLt
      simp only [exponent_left] at h
      split_ifs at h with hi
      · have hk : k.val = 0 := by omega
        rcases k with ⟨v,hv⟩
        change v = 0 at hk
        subst v
        rfl
      · omega
    | inr j =>
      have h := k.isLt
      simp only [exponent_right] at h
      split_ifs at h with hj
      · have hk : k.val = 0 := by omega
        rcases k with ⟨v,hv⟩
        change v = 0 at hk
        subst v
        rfl
      · omega
  right_inv x := by cases x <;> rfl

theorem inverse_label {n : ℕ} (I J : Finset (Fin n)) (x : I ⊕ J) :
    ((equivalence I J).symm x).1 = Sum.map Subtype.val Subtype.val x := by
  cases x <;> rfl

end OccurrenceSquarefreeEquiv
#print axioms OccurrenceSquarefreeEquiv.equivalence
