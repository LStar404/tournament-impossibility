import AssignmentDeletionExponent
import PairingMomentRecurrence

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq

namespace OptionPairingDeletion
open PairingDeletion SymmetricPairingTransport AssignmentDeletionExponent
variable {V : Type*}

def partnerEquiv : V ≃ {x : Option V // x ≠ none} where
  toFun x := ⟨some x,Option.some_ne_none x⟩
  invFun x := x.val.get (Option.isSome_iff_ne_none.mpr x.property)
  left_inv x := rfl
  right_inv := by rintro ⟨x,hx⟩; cases x with
    | none => exact (hx rfl).elim
    | some x => rfl

def restEquiv (x : V) : {y : V // y ≠ x} ≃ Rest (none : Option V) (some x) where
  toFun y := ⟨some y.val,Option.some_ne_none _,fun he => y.property (Option.some.inj he)⟩
  invFun y := ⟨y.val.get (Option.isSome_iff_ne_none.mpr y.property.1),by
    rcases y with ⟨y,hy⟩
    cases y with
    | none => exact (hy.1 rfl).elim
    | some z => exact fun he => hy.2 (congrArg some he)⟩
  left_inv y := rfl
  right_inv := by rintro ⟨y,hy⟩; cases y with
    | none => exact (hy.1 rfl).elim
    | some z => rfl

variable {L S : Type*} [Fintype L] [Fintype V] [CommSemiring S]

theorem option_moment (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (i : L) (a : V → L) :
    moment (fun x y : Option V => C (optionLabel i a x) (optionLabel i a y))
      (fun x y => hs _ _) =
    ∑ x : V, C i (a x) *
      moment (fun y z : {y : V // y ≠ x} => C (a y.val) (a z.val)) (fun y z => hs _ _) := by
  letI : DecidableEq (Option V) := Classical.typeDecidableEq _
  rw [PairingMomentRecurrence.moment_recurrence _ _ none]
  rw [← partnerEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change C i (a x) * _ = C i (a x) * _
  congr 1
  have hh := moment_transport (restEquiv x).symm
    (fun y z : Rest (none : Option V) (some x) => C (optionLabel i a y.val) (optionLabel i a z.val))
    (fun y z => hs _ _)
  exact hh

end OptionPairingDeletion
#print axioms OptionPairingDeletion.option_moment
