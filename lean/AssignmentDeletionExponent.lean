import LinearSourceOccurrences

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace AssignmentDeletionExponent
open LinearSourceOccurrences OccurrenceWickPolynomial
variable {L V : Type*} [Fintype L] [Fintype V]

theorem delete_add (a : V → L) (x : V) :
    exponent a = Finsupp.single (a x) 1 + exponent (fun y : {y : V // y ≠ x} => a y) := by
  classical
  unfold exponent
  rw [← Fintype.sum_subtype_add_sum_subtype (fun y : V => y = x) (fun y => Finsupp.single (a y) 1)]
  congr 1
  simp only [Fintype.sum_unique]
  rw [(default : {y : V // y = x}).property]

theorem delete_sub (a : V → L) (x : V) :
    exponent (fun y : {y : V // y ≠ x} => a y) = exponent a - Finsupp.single (a x) 1 := by
  rw [delete_add a x]
  simp

def optionLabel (i : L) (a : V → L) : Option V → L
  | none => i
  | some x => a x

theorem option_exponent (i : L) (a : V → L) :
    exponent (optionLabel i a) = Finsupp.single i 1 + exponent a := by
  simp [exponent, Fintype.sum_option, optionLabel]

def fibreEquiv (d : L →₀ ℕ) (i : L) :
    {x : Occ d // x.1 = i} ≃ Fin (d i) where
  toFun x := x.property ▸ x.val.2
  invFun k := ⟨⟨i,k⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,k⟩,h⟩; dsimp at h; subst j; rfl
  right_inv k := rfl

theorem occurrence_exponent (d : L →₀ ℕ) :
    exponent (fun x : Occ d => x.1) = d := by
  ext i
  rw [exponent_eq_card, Fintype.card_congr (fibreEquiv d i)]
  exact Fintype.card_fin _

end AssignmentDeletionExponent
#print axioms AssignmentDeletionExponent.delete_sub
#print axioms AssignmentDeletionExponent.occurrence_exponent
