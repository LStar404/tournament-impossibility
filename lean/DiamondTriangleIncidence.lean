import DiamondGap

/-! Actual unordered tournament diamonds and cyclic triples. -/
namespace DiamondTriangleIncidence
open Finset DiamondGap
variable {V : Type*} [DecidableEq V]

/-- A cyclic unordered triple. Equal cyclic signs may be +1 or -1;
reversing the enumeration converts the latter to a positive directed cycle. -/
def IsCyclic (T : Tournament V) (s : Finset V) : Prop :=
  s.card=3 ∧ ∃ a b c, s={a,b,c} ∧ T.S a b=T.S b c ∧ T.S b c = -T.S a c

lemma isCyclic_iff_positive (T : Tournament V) (s : Finset V) :
    IsCyclic T s ↔ s.card=3 ∧ ∃ a b c, s={a,b,c} ∧
      T.S a b=1 ∧ T.S b c=1 ∧ T.S c a=1 := by
  constructor
  · rintro ⟨hc,a,b,c,hs,hab,hbc⟩
    have hne : a ≠ b := by
      intro he
      subst b
      by_cases hac : a=c
      · subst c; simp [hs] at hc
      · rcases T.unit a c hac with h|h <;> rw [T.diagonal,h] at hab <;> norm_num at hab
    rcases T.unit a b hne with h|h
    · refine ⟨hc,a,b,c,hs,h,?_,?_⟩
      · omega
      · have := T.skew c a; omega
    · refine ⟨hc,a,c,b,?_,?_,?_,?_⟩
      · rw [hs]; ext x; simp only [mem_insert, mem_singleton]; tauto
      · omega
      · have := T.skew c b; omega
      · have := T.skew b a; omega
  · rintro ⟨hc,a,b,c,hs,hab,hbc,hca⟩
    refine ⟨hc,a,b,c,hs,?_,?_⟩
    · omega
    · have := T.skew a c; omega

noncomputable def cyclicTriangles [Fintype V] (T : Tournament V) : Finset (Finset V) :=
  by classical exact univ.powerset.filter (IsCyclic T)

lemma mem_cyclicTriangles [Fintype V] (T : Tournament V) (s : Finset V) :
    s ∈ cyclicTriangles T ↔ IsCyclic T s := by
  classical
  simp [cyclicTriangles]

/-- The already-verified ordinary diamond pattern supplies a real cyclic subtriple. -/
theorem diamond_contains_cycle (T : Tournament V) {s : Finset V} (hs : T.IsDiamond s) :
    ∃ t, IsCyclic T t ∧ t ⊆ s := by
  obtain ⟨hc,a,b,c,d,rfl,hq⟩ := hs
  have hd := T.quad_distinct a b c d hq
  have hp := (T.quad_iff_pattern a b c d hd.1 hd.2.1 hd.2.2.1
    hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2).mp hq
  rcases hp with h|h|h|h
  · refine ⟨{b,c,d}, ⟨?_, b,c,d,rfl,h.2.2.1,h.2.2.2⟩, ?_⟩
    · simp [hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2]
    · intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
  · refine ⟨{a,c,d}, ⟨?_, a,c,d,rfl,h.2.2.1,h.2.2.2⟩, ?_⟩
    · simp [hd.2.1, hd.2.2.1, hd.2.2.2.2.2]
    · intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
  · refine ⟨{a,b,d}, ⟨?_, a,b,d,rfl,h.2.2.1,h.2.2.2⟩, ?_⟩
    · simp [hd.1, hd.2.2.1, hd.2.2.2.2.1]
    · intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
  · refine ⟨{a,b,c}, ⟨?_, a,b,c,rfl,h.2.2.1,h.2.2.2⟩, ?_⟩
    · simp [hd.1, hd.2.1, hd.2.2.2.1]
    · intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto

noncomputable def extensions [Fintype V] (t : Finset V) : Finset (Finset V) :=
  (univ \ t).image fun v => insert v t

lemma card_extensions_le [Fintype V] (t : Finset V) :
    (extensions t).card ≤ Fintype.card V-t.card := by
  classical
  calc
    (extensions t).card ≤ (univ \ t).card := card_image_le
    _ = Fintype.card V-t.card := by rw [card_sdiff_of_subset (subset_univ _), card_univ]

lemma mem_extensions_of_subset [Fintype V] (t s : Finset V)
    (hts : t ⊆ s) (hcard : t.card+1=s.card) : s ∈ extensions t := by
  classical
  obtain ⟨v,hv,he⟩ := exists_eq_insert_iff.mpr ⟨hts,hcard⟩
  apply mem_image.mpr
  exact ⟨v, by simp [hv], he⟩

/-- D counts the existing unordered four-sets, t counts actual cyclic three-sets.
Every diamond is covered by extending one of its cyclic triples by one vertex. -/
theorem diamonds_le_triangles [Fintype V] (T : Tournament V) :
    T.diamonds.card ≤ (Fintype.card V-3)*(cyclicTriangles T).card := by
  classical
  have hcover : T.diamonds ⊆ (cyclicTriangles T).biUnion extensions := by
    intro s hs
    have hds := (T.mem_diamonds s).mp hs
    obtain ⟨t,ht,hts⟩ := diamond_contains_cycle T hds
    apply mem_biUnion.mpr
    refine ⟨t,(mem_cyclicTriangles T t).mpr ht,?_⟩
    exact mem_extensions_of_subset t s hts (by rw [ht.1,hds.1])
  calc
    T.diamonds.card ≤ ((cyclicTriangles T).biUnion extensions).card := card_le_card hcover
    _ ≤ ∑ t ∈ cyclicTriangles T, (extensions t).card := card_biUnion_le
    _ ≤ ∑ t ∈ cyclicTriangles T, (Fintype.card V-3) := by
      apply sum_le_sum
      intro t ht
      have hc := ((mem_cyclicTriangles T t).mp ht).1
      simpa [hc] using card_extensions_le t
    _ = (Fintype.card V-3)*(cyclicTriangles T).card := by simp [Nat.mul_comm]

end DiamondTriangleIncidence
#print axioms DiamondTriangleIncidence.diamond_contains_cycle
#print axioms DiamondTriangleIncidence.diamonds_le_triangles
