import TournamentComponents
import StrongTournamentTriangles
noncomputable section
namespace TournamentComponentBlocks
open Finset VectorWeakMajorization TournamentComponents
variable {n : ℕ} (B : Tournament n)

def Fiber (C : Component B) := {v : Fin n // componentOf B v = C}
instance fiberFintype (C : Component B) : Fintype (Fiber B C) := by
  classical
  exact inferInstanceAs (Fintype {v : Fin n // componentOf B v = C})
instance fiberDecidableEq (C : Component B) : DecidableEq (Fiber B C) := Classical.decEq _

def size (C : Component B) : ℕ := Fintype.card (Fiber B C)
def fiberEquiv (C : Component B) : Fin (size B C) ≃ Fiber B C :=
  (Fintype.equivFin (Fiber B C)).symm
def embed (C : Component B) (i : Fin (size B C)) : Fin n := (fiberEquiv B C i).val
lemma embed_injective (C : Component B) : Function.Injective (embed B C) := by
  intro i j hij
  apply (fiberEquiv B C).injective
  exact Subtype.ext hij

/-- Actual induced sign matrix on the vertices of one actual SCC. -/
def induced (C : Component B) : Tournament (size B C) where
  entry i j := B.entry (embed B C i) (embed B C j)
  skew i j := B.skew _ _
  unit i j hij := B.unit _ _ (fun h => hij (embed_injective B C h))

/-- Every actual path between vertices of one SCC lifts to that induced fiber.
No induced strong-connectivity assumption is made. -/
lemma path_in_fiber (C : Component B) {a b : Fin n}
    (ha : componentOf B a = C) (hb : componentOf B b = C) (h : Reach B a b) :
    Relation.ReflTransGen (fun u v : Fiber B C => Edge B u.val v.val)
      (⟨a,ha⟩ : Fiber B C) (⟨b,hb⟩ : Fiber B C) := by
  revert hb
  induction h with
  | refl => intro hb; exact Relation.ReflTransGen.refl
  | @tail c b hac hcb ih =>
    intro hb
    have hba : Reach B b a := ((component_eq_iff B a b).mp (ha.trans hb.symm)).2
    have hca : Reach B c a := (reach_edge B hcb).trans hba
    have hc : componentOf B c = C :=
      ((component_eq_iff B a c).mpr ⟨hac,hca⟩).symm.trans ha
    exact (ih hc).tail hcb

/-- Every finite induced SCC tournament really is strongly connected. -/
theorem induced_strong (C : Component B) : StrongTournamentTriangles.Strong (induced B C) := by
  intro i j
  let a := fiberEquiv B C i
  let b := fiberEquiv B C j
  have hab : Reach B a.val b.val :=
    ((component_eq_iff B a.val b.val).mp (a.property.trans b.property.symm)).1
  have hp := path_in_fiber B C a.property b.property hab
  have hh := Relation.ReflTransGen.lift ((fiberEquiv B C).symm)
    (p := fun u v => (induced B C).entry u v = 1)
    (by
      intro u v huv
      simpa only [Function.onFun, induced, embed, Edge, Equiv.apply_symm_apply] using huv) a b hp
  simpa only [Function.onFun, a, b, Equiv.symm_apply_apply] using hh

/-- The actual injection of ordered cyclic triples into the global tournament. -/
theorem induced_cycleCount_le (C : Component B) :
    TournamentSourceEnergy.cycleCount (induced B C) ≤ TournamentSourceEnergy.cycleCount B := by
  classical
  let f : (Fin (size B C) × Fin (size B C) × Fin (size B C)) →
      (Fin n × Fin n × Fin n) := fun t =>
        (embed B C t.1, embed B C t.2.1, embed B C t.2.2)
  let S := univ.filter (fun t : Fin (size B C) × Fin (size B C) × Fin (size B C) =>
    (induced B C).entry t.1 t.2.1 = 1 ∧ (induced B C).entry t.2.1 t.2.2 = 1 ∧
      (induced B C).entry t.2.2 t.1 = 1)
  let U := univ.filter (fun t : Fin n × Fin n × Fin n =>
    B.entry t.1 t.2.1 = 1 ∧ B.entry t.2.1 t.2.2 = 1 ∧ B.entry t.2.2 t.1 = 1)
  have hmap : Set.MapsTo f (↑S : Set _) (↑U : Set _) := by
    intro t ht
    have hh := (mem_filter.mp ht).2
    exact mem_filter.mpr ⟨mem_univ _, hh⟩
  have hinj : (↑S : Set _).InjOn f := by
    intro u hu v hv he
    apply Prod.ext
    · exact embed_injective B C (congrArg Prod.fst he)
    · apply Prod.ext
      · exact embed_injective B C (congrArg (fun t => t.2.1) he)
      · exact embed_injective B C (congrArg (fun t => t.2.2) he)
  exact card_le_card_of_injOn f hmap hinj

/-- Each actual SCC has size at most the global ordered cycle count whenever
that count is positive. Singleton SCCs are included, without assuming size≥2. -/
theorem component_size_le_cycleCount (C : Component B)
    (hpos : 0 < TournamentSourceEnergy.cycleCount B) :
    size B C ≤ TournamentSourceEnergy.cycleCount B := by
  by_cases hn : 2 ≤ size B C
  · exact le_trans
      (StrongTournamentTriangles.card_le_cycleCount (induced B C) (induced_strong B C) hn)
      (induced_cycleCount_le B C)
  · omega
end TournamentComponentBlocks
#print axioms TournamentComponentBlocks.induced_strong
#print axioms TournamentComponentBlocks.induced_cycleCount_le
#print axioms TournamentComponentBlocks.component_size_le_cycleCount
