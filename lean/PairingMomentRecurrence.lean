import PairingDeletion

noncomputable section
open scoped BigOperators
namespace PairingMomentRecurrence
open PairingDeletion FinitePairingTransport SymmetricPairingTransport
attribute [local instance] Classical.typeDecidableEq

theorem edges_insert {V : Type*} [Fintype V] (o s : V) (hs : s ≠ o)
    (q : Pairing (Rest o s)) :
    edges (PairingDeletion.insert o s hs q) = Insert.insert (Sym2.mk o s)
      ((edges q).image (Sym2.map (Subtype.val : Rest o s → V))) := by
  ext b
  simp only [edges, Finset.mem_image, Finset.mem_univ, true_and,Finset.mem_insert]
  constructor
  · rintro ⟨x,rfl⟩
    change Sym2.mk x (insertFun o s q x) = Sym2.mk o s ∨ _
    by_cases hx : x=o
    · subst x
      left
      simp [insertFun]
    by_cases hxs : x=s
    · subst x
      left
      simp [insertFun,hs,Sym2.eq_swap]
    · right
      refine ⟨Sym2.mk (⟨x,hx,hxs⟩ : Rest o s) (q.val ⟨x,hx,hxs⟩),
        ⟨⟨x,hx,hxs⟩,rfl⟩,?_⟩
      change Sym2.mk x (q.val ⟨x,hx,hxs⟩).val = Sym2.mk x (insertFun o s q x)
      simp [insertFun,hx,hxs]
  · rintro (h | ⟨b,⟨x,rfl⟩,rfl⟩)
    · subst b
      refine ⟨o,?_⟩
      change Sym2.mk o (insertFun o s q o) = _
      simp [insertFun]
    · refine ⟨x.val,?_⟩
      change Sym2.mk x.val (insertFun o s q x.val) = _
      simp [insertFun,x.property.1,x.property.2]

theorem inserted_edge_not_mem {V : Type*} [Fintype V] (o s : V)
    (q : Pairing (Rest o s)) :
    Sym2.mk o s ∉ (edges q).image (Sym2.map (Subtype.val : Rest o s → V)) := by
  intro h
  simp only [edges, Finset.mem_image, Finset.mem_univ,true_and] at h
  obtain ⟨b,⟨x,rfl⟩,hx⟩ := h
  have he : Sym2.mk x.val (q.val x).val = Sym2.mk o s := hx
  rcases Sym2.eq_iff.mp he with h | h
  · exact x.property.1 h.1
  · exact (q.val x).property.1 h.2

theorem weight_insert {V S : Type*} [Fintype V] [CommSemiring S]
    (C : V → V → S) (hc : ∀ x y, C x y = C y x)
    (o s : V) (hs : s ≠ o) (q : Pairing (Rest o s)) :
    SymmetricPairingTransport.weight C hc (PairingDeletion.insert o s hs q) = C o s *
      SymmetricPairingTransport.weight (fun x y : Rest o s => C x.val y.val) (fun x y => hc _ _) q := by
  unfold SymmetricPairingTransport.weight
  rw [edges_insert,Finset.prod_insert (inserted_edge_not_mem o s q)]
  rw [Finset.prod_image]
  · simp only [Sym2.lift_mk]
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    induction b using Sym2.ind with
    | _ x y => rfl
  · intro a ha b hb h
    exact Sym2.map.injective Subtype.val_injective h

/-- All-orders deletion recurrence derived from the actual pairing
bijection and actual unordered-edge factorization. -/
theorem moment_recurrence {V S : Type*} [Fintype V] [CommSemiring S]
    (C : V → V → S) (hc : ∀ x y, C x y = C y x) (o : V) :
    moment C hc = ∑ s : {x : V // x ≠ o}, C o s.val *
      moment (fun x y : Rest o s.val => C x.val y.val) (fun x y => hc _ _) := by
  classical
  unfold moment
  have h := Fintype.sum_equiv (deletionEquiv o)
    (fun d => SymmetricPairingTransport.weight C hc (assemble o d)) (fun p => SymmetricPairingTransport.weight C hc p) (fun d => rfl)
  rw [← h, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact weight_insert C hc o s.val s.property q

end PairingMomentRecurrence
#print axioms PairingMomentRecurrence.moment_recurrence
