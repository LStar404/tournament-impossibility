import PartialMatchingAffine

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PartialMatchingInvolution
open PartialMatchingAffine FinitePairingTransport
variable {V : Type*} [Fintype V]

def partner (p : PartialPairing V) (x : V) : V :=
  if hx : x∈p.1 then (p.2.val ⟨x,hx⟩).val else x

theorem partner_involutive (p : PartialPairing V) : Function.Involutive (partner p) := by
  intro x
  by_cases hx : x∈p.1
  · have hxx : partner p x=(p.2.val ⟨x,hx⟩).val := by simp only [partner,dif_pos hx]
    rw [hxx]
    have hy := (p.2.val ⟨x,hx⟩).property
    rw [partner,dif_pos hy]
    exact congrArg Subtype.val (p.2.property.1 ⟨x,hx⟩)
  · simp [partner,hx]

def permutation (p : PartialPairing V) : Equiv.Perm V where
  toFun := partner p
  invFun := partner p
  left_inv := partner_involutive p
  right_inv := partner_involutive p

theorem moved_iff (p : PartialPairing V) (x : V) : permutation p x ≠ x ↔ x∈p.1 := by
  change partner p x ≠ x ↔ _
  by_cases hx : x∈p.1
  · simp only [partner,dif_pos hx,hx,iff_true]
    intro hh
    apply p.2.property.2 ⟨x,hx⟩
    exact Subtype.ext hh
  · simp [partner,hx]

abbrev Involution (V : Type*) := {q : Equiv.Perm V // Function.Involutive q}

def moved (q : Involution V) : Finset V := Finset.univ.filter (fun x => q.val x ≠ x)

theorem partner_mem (q : Involution V) (x : moved q) : q.val x.val ∈ moved q := by
  simp only [moved,Finset.mem_filter,Finset.mem_univ,true_and] at *
  have hx := (Finset.mem_filter.mp x.property).2
  intro hh
  apply hx
  have hi := q.property x.val
  rw [hh] at hi
  exact hi

def restricted (q : Involution V) : Pairing (moved q) :=
  ⟨{ toFun := fun x => ⟨q.val x.val,partner_mem q x⟩
     invFun := fun x => ⟨q.val x.val,partner_mem q x⟩
     left_inv := fun x => Subtype.ext (q.property x.val)
     right_inv := fun x => Subtype.ext (q.property x.val) },
   ⟨fun x => Subtype.ext (q.property x.val),fun x hx =>
     (Finset.mem_filter.mp x.property).2 (congrArg Subtype.val hx)⟩⟩

def fromInvolution (q : Involution V) : PartialPairing V := ⟨moved q,restricted q⟩
def toInvolution (p : PartialPairing V) : Involution V := ⟨permutation p,partner_involutive p⟩

theorem from_to_support (p : PartialPairing V) : moved (toInvolution p)=p.1 := by
  ext x
  simp [moved,toInvolution,moved_iff]

theorem to_from (q : Involution V) : toInvolution (fromInvolution q)=q := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change partner (fromInvolution q) x=q.val x
  by_cases hx : q.val x=x
  · simp [partner,fromInvolution,moved,hx]
  · have hm : x∈moved q := by simp [moved,hx]
    simp [partner,fromInvolution,hm,restricted]
    rfl

theorem to_injective : Function.Injective (toInvolution (V:=V)) := by
  intro p q he
  have hs : p.1=q.1 := by
    rw [← from_to_support p,← from_to_support q,he]
  rcases p with ⟨s,p⟩
  rcases q with ⟨t,q⟩
  dsimp at hs
  subst t
  apply congrArg (Sigma.mk s)
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have hh := congrArg (fun z : Involution V => z.val x.val) he
  change partner ⟨s,p⟩ x.val=partner ⟨s,q⟩ x.val at hh
  simpa only [partner,x.property,dite_true] using hh

theorem from_to (p : PartialPairing V) : fromInvolution (toInvolution p)=p :=
  to_injective (to_from (toInvolution p))

def equivalence : PartialPairing V ≃ Involution V where
  toFun := toInvolution
  invFun := fromInvolution
  left_inv := from_to
  right_inv := to_from

end PartialMatchingInvolution
#print axioms PartialMatchingInvolution.to_from
#print axioms PartialMatchingInvolution.moved_iff

#print axioms PartialMatchingInvolution.from_to
