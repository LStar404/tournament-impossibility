import Mathlib

namespace DiamondGap

def pf (a b c d e f : ℤ) : ℤ := a*f-b*e+c*d

def sign (b : Bool) : ℤ := if b then 1 else -1

/-- Exhaustive five-vertex tournament check, proved by kernel reduction. -/
theorem local_bool : ∀ a b c d e f g h i j : Bool,
    pf (sign a) (sign b) (sign c) (sign d) (sign e) (sign f) ^ 2 = 9 →
    pf (sign g) (sign h) (sign i) (sign a) (sign b) (sign d) ^ 2 = 9 ∨
    pf (sign g) (sign h) (sign j) (sign a) (sign c) (sign e) ^ 2 = 9 ∨
    pf (sign g) (sign i) (sign j) (sign b) (sign c) (sign f) ^ 2 = 9 ∨
    pf (sign h) (sign i) (sign j) (sign d) (sign e) (sign f) ^ 2 = 9 := by decide

lemma exists_sign (x : ℤ) (hx : x = 1 ∨ x = -1) : ∃ b, x = sign b := by
  rcases hx with rfl | rfl
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

/-- A source or sink joined to a cyclic triangle, in edge order
`ab, ac, ad, bc, bd, cd`. Equality of outgoing signs means source or sink. -/
def diamondPattern (a b c d e f : ℤ) : Prop :=
  (a = b ∧ b = c ∧ d = f ∧ f = -e) ∨
  (-a = d ∧ d = e ∧ b = f ∧ f = -c) ∨
  (-b = -d ∧ -d = f ∧ a = e ∧ e = -c) ∨
  (-c = -e ∧ -e = -f ∧ a = d ∧ d = -b)

instance (a b c d e f : ℤ) : Decidable (diamondPattern a b c d e f) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem pattern_bool : ∀ a b c d e f : Bool,
    pf (sign a) (sign b) (sign c) (sign d) (sign e) (sign f) ^ 2 = 9 ↔
    diamondPattern (sign a) (sign b) (sign c) (sign d) (sign e) (sign f) := by decide

structure Tournament (V : Type*) where
  S : V → V → ℤ
  skew : ∀ a b, S a b = - S b a
  unit : ∀ a b, a ≠ b → S a b = 1 ∨ S a b = -1

namespace Tournament
variable {V : Type*} [DecidableEq V]

def quad (T : Tournament V) (a b c d : V) : ℤ :=
  pf (T.S a b) (T.S a c) (T.S a d) (T.S b c) (T.S b d) (T.S c d)

def IsDiamond (T : Tournament V) (s : Finset V) : Prop :=
  s.card = 4 ∧ ∃ a b c d, s = {a,b,c,d} ∧ T.quad a b c d ^ 2 = 9

lemma diagonal (T : Tournament V) (v : V) : T.S v v = 0 := by
  have := T.skew v v
  omega

lemma quad_distinct (T : Tournament V) (a b c d : V)
    (h : T.quad a b c d ^ 2 = 9) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hz := T.diagonal
  have hs := T.skew
  dsimp [quad, pf] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> subst_vars
  all_goals simp only [hz, zero_mul, mul_zero, sub_zero, add_zero] at h
  · ring_nf at h
    norm_num at h
  · rw [hs c b] at h
    ring_nf at h
    norm_num at h
  · rw [hs d b, hs d c] at h
    ring_nf at h
    norm_num at h
  · ring_nf at h
    norm_num at h
  · rw [hs d c] at h
    ring_nf at h
    norm_num at h
  · ring_nf at h
    norm_num at h


lemma diamond_of_quad (T : Tournament V) (a b c d : V)
    (h : T.quad a b c d ^ 2 = 9) : T.IsDiamond {a,b,c,d} := by
  have hd := T.quad_distinct a b c d h
  refine ⟨?_, a,b,c,d,rfl,h⟩
  simp [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2]

#print axioms DiamondGap.local_bool

/-- Identification with the ordinary tournament diamond (source/sink plus cycle),
not an abstract hypergraph or a graph inferred from a color representation. -/
theorem quad_iff_pattern (T : Tournament V) (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    T.quad a b c d ^ 2 = 9 ↔
    diamondPattern (T.S a b) (T.S a c) (T.S a d) (T.S b c) (T.S b d) (T.S c d) := by
  obtain ⟨x1, hx1⟩ := exists_sign _ (T.unit a b hab)
  obtain ⟨x2, hx2⟩ := exists_sign _ (T.unit a c hac)
  obtain ⟨x3, hx3⟩ := exists_sign _ (T.unit a d had)
  obtain ⟨x4, hx4⟩ := exists_sign _ (T.unit b c hbc)
  obtain ⟨x5, hx5⟩ := exists_sign _ (T.unit b d hbd)
  obtain ⟨x6, hx6⟩ := exists_sign _ (T.unit c d hcd)
  simp only [quad, hx1,hx2,hx3,hx4,hx5,hx6]
  exact pattern_bool x1 x2 x3 x4 x5 x6


lemma local_extension (T : Tournament V) (v a b c d : V)
    (ha : v ≠ a) (hb : v ≠ b) (hc : v ≠ c) (hd : v ≠ d)
    (h : T.quad a b c d ^ 2 = 9) :
    T.quad v a b c ^ 2 = 9 ∨ T.quad v a b d ^ 2 = 9 ∨
    T.quad v a c d ^ 2 = 9 ∨ T.quad v b c d ^ 2 = 9 := by
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := T.quad_distinct a b c d h
  obtain ⟨x1, hx1⟩ := exists_sign _ (T.unit a b hab)
  obtain ⟨x2, hx2⟩ := exists_sign _ (T.unit a c hac)
  obtain ⟨x3, hx3⟩ := exists_sign _ (T.unit a d had)
  obtain ⟨x4, hx4⟩ := exists_sign _ (T.unit b c hbc)
  obtain ⟨x5, hx5⟩ := exists_sign _ (T.unit b d hbd)
  obtain ⟨x6, hx6⟩ := exists_sign _ (T.unit c d hcd)
  obtain ⟨x7, hx7⟩ := exists_sign _ (T.unit v a ha)
  obtain ⟨x8, hx8⟩ := exists_sign _ (T.unit v b hb)
  obtain ⟨x9, hx9⟩ := exists_sign _ (T.unit v c hc)
  obtain ⟨x10, hx10⟩ := exists_sign _ (T.unit v d hd)
  simp only [quad, hx1,hx2,hx3,hx4,hx5,hx6,hx7,hx8,hx9,hx10] at h ⊢
  exact local_bool x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 h

/-- An actual tournament diamond forces every vertex to lie in a diamond. -/
theorem diamond_covers (T : Tournament V) {s : Finset V}
    (hs : T.IsDiamond s) (v : V) : ∃ t, T.IsDiamond t ∧ v ∈ t := by
  by_cases hv : v ∈ s
  · exact ⟨s,hs,hv⟩
  obtain ⟨_,a,b,c,d,rfl,h⟩ := hs
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  rcases T.local_extension v a b c d hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 h with h | h | h | h
  · exact ⟨{v,a,b,c}, T.diamond_of_quad v a b c h, by simp⟩
  · exact ⟨{v,a,b,d}, T.diamond_of_quad v a b d h, by simp⟩
  · exact ⟨{v,a,c,d}, T.diamond_of_quad v a c d h, by simp⟩
  · exact ⟨{v,b,c,d}, T.diamond_of_quad v b c d h, by simp⟩

noncomputable def diamonds [Fintype V] (T : Tournament V) : Finset (Finset V) :=
  by classical exact (Finset.univ.powerset).filter T.IsDiamond

lemma mem_diamonds [Fintype V] (T : Tournament V) (s : Finset V) :
    s ∈ T.diamonds ↔ T.IsDiamond s := by
  classical
  simp [diamonds]

/-- Universal positive diamond gap, counting unordered four-vertex sets. -/
theorem positive_gap [Fintype V] (T : Tournament V)
    (h : 0 < T.diamonds.card) : Fintype.card V ≤ 4 * T.diamonds.card := by
  classical
  obtain ⟨s, hs⟩ := Finset.card_pos.mp h
  have hcover : T.diamonds.biUnion id = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨t,ht,hv⟩ := T.diamond_covers ((T.mem_diamonds s).mp hs) v
    exact Finset.mem_biUnion.mpr ⟨t, (T.mem_diamonds t).mpr ht, hv⟩
  calc
    Fintype.card V = (T.diamonds.biUnion id).card := by rw [hcover, Finset.card_univ]
    _ ≤ ∑ s ∈ T.diamonds, s.card := Finset.card_biUnion_le
    _ = ∑ _s ∈ T.diamonds, 4 := Finset.sum_congr rfl (fun s hs => ((T.mem_diamonds s).mp hs).1)
    _ = 4 * T.diamonds.card := by simp [Nat.mul_comm]

/-- Unconditional dichotomy, including all orders smaller than four. -/
theorem zero_or_gap [Fintype V] (T : Tournament V) :
    T.diamonds.card = 0 ∨ Fintype.card V ≤ 4 * T.diamonds.card := by
  by_cases h : T.diamonds.card = 0
  · exact Or.inl h
  · exact Or.inr (T.positive_gap (Nat.pos_of_ne_zero h))

#print axioms quad_iff_pattern
#print axioms diamond_covers
#print axioms positive_gap
#print axioms zero_or_gap
end Tournament
end DiamondGap
