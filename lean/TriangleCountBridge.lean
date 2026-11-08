import DiamondTriangleIncidence
import TournamentSourceEnergy
namespace TriangleCountBridge
open Finset DiamondGap DiamondTriangleIncidence
variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def toReal {n : ℕ} (T : Tournament (Fin n)) : VectorWeakMajorization.Tournament n where
  entry i j := (T.S i j : ℝ)
  skew i j := by exact_mod_cast T.skew i j
  unit i j hij := by rcases T.unit i j hij with h|h <;> simp [h]

noncomputable def directedTriples (T : Tournament V) : Finset (V × V × V) :=
  univ.filter fun q => T.S q.1 q.2.1=1 ∧ T.S q.2.1 q.2.2=1 ∧ T.S q.2.2 q.1=1

def vertices (q : V × V × V) : Finset V := {q.1,q.2.1,q.2.2}

noncomputable def fibre (T : Tournament V) (s : Finset V) : Finset (V × V × V) :=
  (directedTriples T).filter fun q => vertices q=s

omit [Fintype V] in
lemma positive_distinct (T : Tournament V) {a b c : V}
    (hab : T.S a b=1) (hbc : T.S b c=1) (hca : T.S c a=1) :
    a≠b ∧ a≠c ∧ b≠c := by
  refine ⟨?_,?_,?_⟩ <;> intro he
  · subst b; rw [T.diagonal] at hab; norm_num at hab
  · subst c; rw [T.diagonal] at hca; norm_num at hca
  · subst c; rw [T.diagonal] at hbc; norm_num at hbc

lemma fibre_eq_rotations (T : Tournament V) {a b c : V}
    (hab : T.S a b=1) (hbc : T.S b c=1) (hca : T.S c a=1) :
    fibre T {a,b,c} = {(a,b,c),(b,c,a),(c,a,b)} := by
  classical
  have hba : T.S b a = -1 := by rw [T.skew b a,hab]
  have hcb : T.S c b = -1 := by rw [T.skew c b,hbc]
  have hac : T.S a c = -1 := by rw [T.skew a c,hca]
  have hd := positive_distinct T hab hbc hca
  apply Finset.ext
  intro q
  rcases q with ⟨x,y,z⟩
  constructor
  · intro h
    have hh := mem_filter.mp h
    have hp := (mem_filter.mp hh.1).2
    have hv : ({x,y,z}:Finset V)={a,b,c} := hh.2
    clear h hh
    have hx : x∈({a,b,c}:Finset V) := by rw [← hv]; simp
    have hy : y∈({a,b,c}:Finset V) := by rw [← hv]; simp
    have hz : z∈({a,b,c}:Finset V) := by rw [← hv]; simp
    simp only [mem_insert,mem_singleton] at hx hy hz
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
      rcases hz with rfl|rfl|rfl <;>
      simp_all [T.diagonal]
  · intro h
    simp only [mem_insert,mem_singleton] at h
    rcases h with h|h|h <;> cases h
    all_goals
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩
    all_goals simp [vertices,hab,hbc,hca]
    all_goals apply Finset.ext; intro v; simp only [mem_insert,mem_singleton]; tauto

lemma fibre_card (T : Tournament V) (s : Finset V) (hs : IsCyclic T s) :
    (fibre T s).card=3 := by
  classical
  obtain ⟨hc,a,b,c,rfl,hab,hbc,hca⟩ := (isCyclic_iff_positive T s).mp hs
  rw [fibre_eq_rotations T hab hbc hca]
  have hd := positive_distinct T hab hbc hca
  simp [hd.1,hd.2.1,hd.2.2,Ne.symm hd.1,Ne.symm hd.2.1,Ne.symm hd.2.2]

lemma union_fibres (T : Tournament V) :
    (cyclicTriangles T).biUnion (fibre T) = directedTriples T := by
  classical
  apply Finset.ext
  intro q
  constructor
  · intro h
    obtain ⟨s,hs,hq⟩ := mem_biUnion.mp h
    exact (mem_filter.mp hq).1
  · intro h
    rcases q with ⟨a,b,c⟩
    have hp := h
    simp only [directedTriples,mem_filter,mem_univ,true_and] at hp
    have hd := positive_distinct T hp.1 hp.2.1 hp.2.2
    refine mem_biUnion.mpr ⟨{a,b,c},?_,?_⟩
    · apply (mem_cyclicTriangles T _).mpr
      apply (isCyclic_iff_positive T _).mpr
      exact ⟨by simp [hd.1,hd.2.1,hd.2.2],a,b,c,rfl,hp⟩
    · exact mem_filter.mpr ⟨h,rfl⟩

lemma ordered_eq_three_unordered (T : Tournament V) :
    (directedTriples T).card = 3*(cyclicTriangles T).card := by
  classical
  have hdis : (cyclicTriangles T : Set (Finset V)).PairwiseDisjoint (fibre T) := by
    intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    have h1 := (mem_filter.mp hq).2
    have h2 := (mem_filter.mp hq').2
    exact hst (h1.symm.trans h2)
  rw [← union_fibres T,card_biUnion hdis]
  calc
    (∑ s ∈ cyclicTriangles T, (fibre T s).card) = ∑ s ∈ cyclicTriangles T, 3 := by
      apply sum_congr rfl; intro s hs
      exact fibre_card T s ((mem_cyclicTriangles T s).mp hs)
    _ = 3*(cyclicTriangles T).card := by simp [Nat.mul_comm]

/-- The real source-energy ordered count is exactly three times the actual
unordered cyclic-triple count, with no division-defined substitute. -/
theorem real_cycleCount_eq_three {n : ℕ} (T : Tournament (Fin n)) :
    TournamentSourceEnergy.cycleCount (toReal T) = 3*(cyclicTriangles T).card := by
  have he : TournamentSourceEnergy.cycleCount (toReal T) = (directedTriples T).card := by
    unfold TournamentSourceEnergy.cycleCount directedTriples toReal
    congr 1
    apply Finset.ext
    intro q
    simp only [mem_filter, mem_univ, true_and]
    norm_cast
  rw [he,ordered_eq_three_unordered]

/-- Generic finite-carrier interface, including nested sums of SCC carriers. -/
theorem three_diamonds_le_ordered (T : Tournament V) :
    3*T.diamonds.card ≤ (Fintype.card V-3)*(directedTriples T).card := by
  rw [ordered_eq_three_unordered]
  have h := diamonds_le_triangles T
  nlinarith

/-- Exact ordinary-triangle source-energy deficit, now without ordered-count division. -/
theorem source_energy_unordered {n : ℕ} (T : Tournament (Fin n)) :
    TwoBlockEnergy.first (TournamentPowerComparison.matrix (toReal T)) =
      (n : ℝ)*((n : ℝ)^2-1)/3 - 8*((cyclicTriangles T).card : ℝ) := by
  rw [TournamentSourceEnergy.first_eq_reference_sub, real_cycleCount_eq_three]
  push_cast
  ring

end TriangleCountBridge
#print axioms TriangleCountBridge.ordered_eq_three_unordered
#print axioms TriangleCountBridge.real_cycleCount_eq_three

#print axioms TriangleCountBridge.three_diamonds_le_ordered
#print axioms TriangleCountBridge.source_energy_unordered
