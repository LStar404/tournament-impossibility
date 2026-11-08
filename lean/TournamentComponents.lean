import VectorWeakMajorization
noncomputable section
namespace TournamentComponents
open VectorWeakMajorization
variable {n : ℕ} (B : Tournament n)

/-- Actual positive directed edge of the tournament sign matrix. -/
def Edge (a b : Fin n) : Prop := B.entry a b = 1
/-- Reachability by a finite path, including the path of length zero. -/
def Reach (a b : Fin n) : Prop := Relation.ReflTransGen (Edge B) a b
def MutualReach (a b : Fin n) : Prop := Reach B a b ∧ Reach B b a

lemma reach_refl (a : Fin n) : Reach B a a := Relation.ReflTransGen.refl
lemma reach_trans {a b c : Fin n} (hab : Reach B a b) (hbc : Reach B b c) :
    Reach B a c := hab.trans hbc
lemma reach_edge {a b : Fin n} (h : Edge B a b) : Reach B a b :=
  Relation.ReflTransGen.single h

lemma edge_irrefl (a : Fin n) : ¬Edge B a a := by
  simp [Edge, B.diagonal]
lemma edge_total {a b : Fin n} (hab : a ≠ b) : Edge B a b ∨ Edge B b a := by
  rcases B.unit a b hab with h | h
  · exact Or.inl h
  · right
    have hs := B.skew a b
    unfold Edge
    linarith
lemma reach_total (a b : Fin n) : Reach B a b ∨ Reach B b a := by
  by_cases hab : a = b
  · subst b; exact Or.inl (reach_refl B a)
  · rcases edge_total B hab with h | h
    · exact Or.inl (reach_edge B h)
    · exact Or.inr (reach_edge B h)

lemma mutual_refl (a : Fin n) : MutualReach B a a := ⟨reach_refl B a, reach_refl B a⟩
lemma mutual_symm {a b : Fin n} (h : MutualReach B a b) : MutualReach B b a := ⟨h.2,h.1⟩
lemma mutual_trans {a b c : Fin n} (hab : MutualReach B a b) (hbc : MutualReach B b c) :
    MutualReach B a c := ⟨hab.1.trans hbc.1, hbc.2.trans hab.2⟩

def componentSetoid : Setoid (Fin n) where
  r := MutualReach B
  iseqv := ⟨mutual_refl B, fun {_ _} h => mutual_symm B h,
    fun {_ _ _} h1 h2 => mutual_trans B h1 h2⟩

/-- Reachability is independent of representatives within mutual-reach classes. -/
lemma reach_congr {a a' b b' : Fin n}
    (ha : MutualReach B a a') (hb : MutualReach B b b') :
    Reach B a b ↔ Reach B a' b' := by
  constructor
  · intro h; exact ha.2.trans (h.trans hb.1)
  · intro h; exact ha.1.trans (h.trans hb.2)

/-- A one-way reachability relation between distinct components forces the
actual edge in that direction. -/
lemma edge_of_reach_not_reverse {a b : Fin n}
    (hab : Reach B a b) (hba : ¬Reach B b a) : Edge B a b := by
  have hne : a ≠ b := by intro h; subst b; exact hba (reach_refl B a)
  rcases edge_total B hne with h | h
  · exact h
  · exact False.elim (hba (reach_edge B h))

/-- Every cross-component edge has a uniform direction, for all representatives. -/
theorem cross_edge_uniform {a a' b b' : Fin n}
    (ha : MutualReach B a a') (hb : MutualReach B b b')
    (hne : ¬MutualReach B a b) (hab : Edge B a b) : Edge B a' b' := by
  have hreach : Reach B a b := reach_edge B hab
  apply edge_of_reach_not_reverse B ((reach_congr B ha hb).mp hreach)
  intro hrev
  apply hne
  exact ⟨hreach, hb.1.trans (hrev.trans ha.2)⟩

/-- An intermediate vertex of a path between vertices in the same SCC remains
in that SCC. This is the local fact needed for induced strong blocks. -/
theorem intermediate_same_component {a b c : Fin n}
    (hab : MutualReach B a b) (hac : Reach B a c) (hcb : Reach B c b) :
    MutualReach B a c := ⟨hac, hcb.trans hab.2⟩

def Component := Quotient (componentSetoid B)
def componentOf (a : Fin n) : Component B := Quotient.mk _ a

def componentLE (A C : Component B) : Prop := Reach B A.out C.out

instance componentPartialOrder : PartialOrder (Component B) where
  le := componentLE B
  le_refl A := reach_refl B A.out
  le_trans A C D hAC hCD := hAC.trans hCD
  le_antisymm A C hAC hCA := by
    have h : (Quotient.mk (componentSetoid B) A.out : Component B) =
        Quotient.mk (componentSetoid B) C.out := Quotient.sound ⟨hAC,hCA⟩
    exact (Quotient.out_eq A).symm.trans (h.trans (Quotient.out_eq C))

/-- The condensation is a genuine total order, constructed from actual paths. -/
instance componentLinearOrder : LinearOrder (Component B) := by
  classical
  exact { componentPartialOrder B with
    le_total := fun A C => reach_total B A.out C.out
    toDecidableLE := Classical.decRel _ }

instance componentFintype : Fintype (Component B) := by
  classical
  exact Quotient.fintype (componentSetoid B)

lemma component_le_iff (a b : Fin n) :
    componentOf B a ≤ componentOf B b ↔ Reach B a b := by
  exact reach_congr B (Quotient.mk_out (s := componentSetoid B) a)
    (Quotient.mk_out (s := componentSetoid B) b)

lemma component_eq_iff (a b : Fin n) :
    componentOf B a = componentOf B b ↔ MutualReach B a b := Quotient.eq

/-- Strict component order is exactly the uniform positive cross-edge
orientation together with distinctness of the components. -/
theorem component_lt_iff (a b : Fin n) :
    componentOf B a < componentOf B b ↔ Edge B a b ∧ ¬MutualReach B a b := by
  rw [lt_iff_le_not_ge, component_le_iff, component_le_iff]
  constructor
  · intro h
    exact ⟨edge_of_reach_not_reverse B h.1 h.2, fun hh => h.2 hh.2⟩
  · intro h
    exact ⟨reach_edge B h.1, fun hh => h.2 ⟨reach_edge B h.1,hh⟩⟩

/-- Transitivity is a theorem about cross-component actual edges, rather than
an imposed ordering of an assumed block decomposition. -/
theorem cross_edge_trans {a b c : Fin n}
    (hab : Edge B a b) (hbc : Edge B b c)
    (hne : ¬MutualReach B a c) : Edge B a c := by
  have hac := (reach_edge B hab).trans (reach_edge B hbc)
  exact edge_of_reach_not_reverse B hac (fun hca => hne ⟨hac,hca⟩)
end TournamentComponents
#print axioms TournamentComponents.cross_edge_uniform
#print axioms TournamentComponents.component_lt_iff
#print axioms TournamentComponents.cross_edge_trans
