import Mathlib.Tactic

/-!
# A local noncommutative Thue–Morse cancellation lemma

This file proves only the filtered-ring recursion. It does not prove the
polynomial/period cost bounds of tournament kernels, permanent recovery, or R.
The filtration is an explicit hypothesis, not a new axiom.
-/
namespace OrderedCancellation

variable {R : Type*} [Ring R]

/-- A descending multiplicative additive filtration (no commutativity needed). -/
structure Filtration (R : Type*) [Ring R] where
  mem : ℕ → R → Prop
  add : ∀ {n x y}, mem n x → mem n y → mem n (x + y)
  sub : ∀ {n x y}, mem n x → mem n y → mem n (x - y)
  mul : ∀ {m n x y}, mem m x → mem n y → mem (m + n) (x * y)
  lower : ∀ {m n x}, m ≤ n → mem n x → mem m x

/-- Ordered positive/negative blocks; switching signs swaps the children. -/
def blocks (a b : R) : ℕ → R × R
  | 0 => (a, b)
  | n + 1 => let p := blocks a b n; (p.1 * p.2, p.2 * p.1)

lemma product_residual (F : Filtration R) {a b : R}
    (ha : F.mem 1 (a - 1)) (hb : F.mem 1 (b - 1)) :
    F.mem 1 (a * b - 1) := by
  have h := F.lower (by omega : 1 ≤ 1 + 1) (F.mul ha hb)
  have he : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by
    noncomm_ring
  rw [he]
  exact F.add (F.add h ha) hb

/-- Both blocks retain constant term one at every depth. -/
theorem blocks_residual (F : Filtration R) {a b : R}
    (ha : F.mem 1 (a - 1)) (hb : F.mem 1 (b - 1)) (n : ℕ) :
    F.mem 1 ((blocks a b n).1 - 1) ∧
    F.mem 1 ((blocks a b n).2 - 1) := by
  induction n with
  | zero => exact ⟨ha, hb⟩
  | succ n ih =>
    exact ⟨product_residual F ih.1 ih.2, product_residual F ih.2 ih.1⟩

/-- After n recursive doublings the sign-odd difference has order ≥ n+1. -/
theorem difference_order (F : Filtration R) {a b : R}
    (ha : F.mem 1 (a - 1)) (hb : F.mem 1 (b - 1)) (n : ℕ) :
    F.mem (n + 1) ((blocks a b n).1 - (blocks a b n).2) := by
  induction n with
  | zero =>
    have h := F.sub ha hb
    simpa [blocks] using h
  | succ n ih =>
    let p := blocks a b n
    have hb' : F.mem 1 (p.2 - 1) := (blocks_residual F ha hb n).2
    have hleft := F.mul ih hb'
    have hright := F.mul hb' ih
    have hright' : F.mem (n + 1 + 1) ((p.2 - 1) * (p.1 - p.2)) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, p] using hright
    have he : p.1 * p.2 - p.2 * p.1 =
        (p.1 - p.2) * (p.2 - 1) - (p.2 - 1) * (p.1 - p.2) := by
      noncomm_ring
    change F.mem (n + 1 + 1) (p.1 * p.2 - p.2 * p.1)
    rw [he]
    exact F.sub hleft hright'

/-- Any additive observable vanishing at this order sees identical blocks.
For a coefficient functional, its vanishing hypothesis must be supplied. -/
theorem observable_equal {A : Type*} [AddGroup A] (F : Filtration R)
    {a b : R} (ha : F.mem 1 (a - 1)) (hb : F.mem 1 (b - 1))
    (n : ℕ) (observe : R →+ A)
    (vanishes : ∀ x, F.mem (n + 1) x → observe x = 0) :
    observe (blocks a b n).1 = observe (blocks a b n).2 := by
  have h := vanishes _ (difference_order F ha hb n)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

/-- The two complementary recursively ordered Thue–Morse words. -/
def words : ℕ → List Bool × List Bool
  | 0 => ([false], [true])
  | n + 1 => let w := words n; (w.1 ++ w.2, w.2 ++ w.1)

/-- Each depth has exactly the expected number of positions. -/
theorem words_length (n : ℕ) :
    (words n).1.length = 2 ^ n ∧ (words n).2.length = 2 ^ n := by
  induction n with
  | zero => simp [words]
  | succ n ih => simp [words, List.length_append, ih.1, ih.2, pow_succ, Nat.mul_two]

/-- Both sign choices are retained; products are ordered, not commuted. -/
def evaluate (a b : R) (w : List Bool) : R :=
  (w.map fun s => if s then b else a).prod

lemma evaluate_append (a b : R) (u v : List Bool) :
    evaluate a b (u ++ v) = evaluate a b u * evaluate a b v := by
  simp [evaluate]

/-- The recursion is exactly the ordered product over the dyadic words. -/
theorem evaluate_words (a b : R) (n : ℕ) :
    evaluate a b (words n).1 = (blocks a b n).1 ∧
    evaluate a b (words n).2 = (blocks a b n).2 := by
  induction n with
  | zero => simp [words, blocks, evaluate]
  | succ n ih =>
    simp only [words, blocks, evaluate_append, ih.1, ih.2]
    exact ⟨trivial, trivial⟩

/-- Doing q levels first is exactly the same as treating them as two packets.
This identity does not require commutative multiplication. -/
theorem blocks_add (a b : R) (q n : ℕ) :
    blocks a b (q + n) = blocks (blocks a b q).1 (blocks a b q).2 n := by
  induction n with
  | zero => simp [blocks]
  | succ n ih =>
    change ((blocks a b (q + n)).1 * (blocks a b (q + n)).2,
      (blocks a b (q + n)).2 * (blocks a b (q + n)).1) = _
    rw [ih]
    rfl

/-- A finite packet of factors equal to one modulo F₁ has the same property. -/
theorem list_product_residual (F : Filtration R) (xs : List R)
    (h : ∀ x ∈ xs, F.mem 1 (x - 1)) (hz : F.mem 1 0) :
    F.mem 1 (xs.prod - 1) := by
  induction xs with
  | nil => simpa using hz
  | cons x xs ih =>
    simp only [List.prod_cons]
    exact product_residual F (h x (by simp))
      (ih (fun y hy => h y (by simp [hy])))

/-- Expand each high-bit sign into a whole low-position packet. -/
def expandPackets (positive negative : List R) (w : List Bool) : List R :=
  w.flatMap fun s => if s then negative else positive

lemma expandPackets_prod (positive negative : List R) (w : List Bool) :
    (expandPackets positive negative w).prod =
      evaluate positive.prod negative.prod w := by
  induction w with
  | nil => simp [expandPackets, evaluate]
  | cons s w ih =>
    cases s <;> simp_all [expandPackets, evaluate]

omit [Ring R] in
lemma expandPackets_length (positive negative : List R) (w : List Bool)
    (k : ℕ) (hp : positive.length = k) (hn : negative.length = k) :
    (expandPackets positive negative w).length = w.length * k := by
  induction w with
  | nil => simp [expandPackets]
  | cons s w ih =>
    cases s <;> simp_all [expandPackets, Nat.add_mul, Nat.add_comm]

/-- Both expanded words have the original total length 2^r. -/
theorem packet_length (positive negative : List R) (r q : ℕ)
    (hq : q ≤ r) (hp : positive.length = 2 ^ q) (hn : negative.length = 2 ^ q) :
    (expandPackets positive negative (words (r - q)).1).length = 2 ^ r ∧
    (expandPackets positive negative (words (r - q)).2).length = 2 ^ r := by
  rw [expandPackets_length positive negative _ _ hp hn,
    expandPackets_length positive negative _ _ hp hn,
    (words_length (r - q)).1, (words_length (r - q)).2,
    ← pow_add, Nat.sub_add_cancel hq]
  exact ⟨rfl, rfl⟩

/-- Finite low-period packets retain the cancellation order of the remaining
high-bit recursion. In applications q low bits leave r-q high levels.
The packet input is explicit: identifying concrete kernels with these packets
and proving any Taylor-degree cost is NOT part of this theorem. -/
theorem packet_difference_order (F : Filtration R)
    (positive negative : List R)
    (hp : ∀ x ∈ positive, F.mem 1 (x - 1))
    (hn : ∀ x ∈ negative, F.mem 1 (x - 1))
    (hz : F.mem 1 0) (r q : ℕ) (_hq : q ≤ r)
    (_hpLength : positive.length = 2 ^ q)
    (_hnLength : negative.length = 2 ^ q) :
    F.mem (r - q + 1)
      ((expandPackets positive negative (words (r - q)).1).prod -
       (expandPackets positive negative (words (r - q)).2).prod) := by
  rw [expandPackets_prod, expandPackets_prod,
    (evaluate_words positive.prod negative.prod (r - q)).1,
    (evaluate_words positive.prod negative.prod (r - q)).2]
  exact difference_order F (list_product_residual F positive hp hz)
    (list_product_residual F negative hn hz) (r - q)

#print axioms product_residual
#print axioms blocks_residual
#print axioms difference_order
#print axioms observable_equal
#print axioms words_length
#print axioms evaluate_words
#print axioms blocks_add
#print axioms packet_length
#print axioms packet_difference_order
end OrderedCancellation
