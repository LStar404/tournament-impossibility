import SymmetricPairingTransport

noncomputable section
namespace PairingDeletion
open FinitePairingTransport
attribute [local instance] Classical.typeDecidableEq

abbrev Rest {V : Type*} (o s : V) := {x : V // x ≠ o ∧ x ≠ s}

def restrict {V : Type*} (p : Pairing V) (o : V) : Pairing (Rest o (p.val o)) := by
  let f : Rest o (p.val o) → Rest o (p.val o) := fun x => ⟨p.val x.val, by
    constructor
    · intro h
      have hh := congrArg p.val h
      rw [p.property.1] at hh
      exact x.property.2 hh
    · intro h
      exact x.property.1 (p.val.injective h)⟩
  have hf : Function.Involutive f := by
    intro x
    apply Subtype.ext
    exact p.property.1 x.val
  exact ⟨⟨f,f,hf,hf⟩,hf,by
    intro x h
    exact p.property.2 x.val (congrArg Subtype.val h)⟩

def insertFun {V : Type*} (o s : V) (q : Pairing (Rest o s)) (x : V) : V :=
  if h : x=o then s else if h' : x=s then o else (q.val ⟨x,h,h'⟩).val

theorem insert_involutive {V : Type*} (o s : V) (hs : s ≠ o)
    (q : Pairing (Rest o s)) : Function.Involutive (insertFun o s q) := by
  intro x
  by_cases hx : x=o
  · subst x
    simp [insertFun,hs]
  by_cases hxs : x=s
  · subst x
    simp [insertFun,hs]
  have hy := (q.val ⟨x,hx,hxs⟩).property
  simp only [insertFun, dite_eq_right hx, dite_eq_right hxs, dite_eq_right hy.1, dite_eq_right hy.2]
  exact congrArg Subtype.val (q.property.1 ⟨x,hx,hxs⟩)

def insert {V : Type*} (o s : V) (hs : s ≠ o) (q : Pairing (Rest o s)) : Pairing V :=
  ⟨⟨insertFun o s q,insertFun o s q,insert_involutive o s hs q,insert_involutive o s hs q⟩,
    insert_involutive o s hs q,by
      intro x h
      change insertFun o s q x = x at h
      by_cases hx : x=o
      · subst x
        simp [insertFun] at h
        exact hs h
      by_cases hxs : x=s
      · subst x
        simp [insertFun,hs] at h
        exact hs h.symm
      simp only [insertFun,dite_eq_right hx,dite_eq_right hxs] at h
      exact q.property.2 ⟨x,hx,hxs⟩ (Subtype.ext h)⟩

theorem insert_restrict {V : Type*} (p : Pairing V) (o : V) :
    insert o (p.val o) (p.property.2 o) (restrict p o) = p := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change insertFun o (p.val o) (restrict p o) x = p.val x
  by_cases hx : x=o
  · subst x
    simp [insertFun]
  by_cases hxs : x=p.val o
  · subst x
    simp [insertFun,p.property.2 o,p.property.1 o]
  simp only [insertFun,dite_eq_right hx,dite_eq_right hxs]
  rfl

abbrev DeletionData {V : Type*} (o : V) := Σ s : {x : V // x ≠ o}, Pairing (Rest o s.val)

def assemble {V : Type*} (o : V) (d : DeletionData o) : Pairing V :=
  insert o d.1.val d.1.property d.2

theorem assemble_injective {V : Type*} (o : V) : Function.Injective (assemble o) := by
  rintro ⟨s,q⟩ ⟨t,r⟩ h
  have hst : s = t := by
    apply Subtype.ext
    have hh := congrArg (fun p : Pairing V => p.val o) h
    change insertFun o s.val q o = insertFun o t.val r o at hh
    simpa [insertFun] using hh
  cases hst
  congr 1
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have hh := congrArg (fun p : Pairing V => p.val x.val) h
  change insertFun o s.val q x.val = insertFun o s.val r x.val at hh
  simpa [insertFun,x.property.1,x.property.2] using hh

theorem assemble_surjective {V : Type*} (o : V) : Function.Surjective (assemble o) := by
  intro p
  exact ⟨⟨⟨p.val o,p.property.2 o⟩,restrict p o⟩,insert_restrict p o⟩

/-- Actual pairing decomposition, not a recurrence postulate. -/
def deletionEquiv {V : Type*} (o : V) : DeletionData o ≃ Pairing V :=
  Equiv.ofBijective (assemble o) ⟨assemble_injective o,assemble_surjective o⟩

end PairingDeletion
#print axioms PairingDeletion.insert_restrict

#print axioms PairingDeletion.deletionEquiv
