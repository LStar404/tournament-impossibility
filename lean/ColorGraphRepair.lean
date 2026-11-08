import ColorTransportExact
namespace ColorTransport

/-- Ordinary interchange of two adjacent labels. -/
def swapIndex (k i : ℕ) : ℕ := if i = k then k+1 else if i = k+1 then k else i

private theorem swapIndex_succ (k i : ℕ) :
    swapIndex (k+1) (i+1) = swapIndex k i + 1 := by
  unfold swapIndex
  split_ifs <;> omega

private theorem swapIndex_involutive (k i : ℕ) : swapIndex k (swapIndex k i) = i := by
  unfold swapIndex
  split_ifs <;> omega

def swapEquiv (k : ℕ) : Equiv ℕ ℕ where
  toFun := swapIndex k
  invFun := swapIndex k
  left_inv := swapIndex_involutive k
  right_inv := swapIndex_involutive k

private theorem swapIndex_bound (k n i : ℕ) (hk : k+1 < n) :
    swapIndex k i < n ↔ i < n := by
  unfold swapIndex
  split_ifs <;> omega

private theorem adjacent_get (pre tail : List Bool) (a b : Bool) (i : ℕ) :
    (pre ++ b::a::tail).getD (swapIndex pre.length i) false =
      (pre ++ a::b::tail).getD i false := by
  induction pre generalizing i with
  | nil =>
    cases i with
    | zero => simp [swapIndex]
    | succ i => cases i <;> simp [swapIndex]
  | cons c pre ih =>
    cases i with
    | zero => simp [swapIndex]
    | succ i => simpa [swapIndex_succ] using ih i

/-- Sign of the transitive order, with zero diagonal. -/
def orderSign (i j : ℕ) : ℝ := if i < j then 1 else if j < i then -1 else 0

def isPair (a b i j : ℕ) : Prop := (i=a ∧ j=b) ∨ (i=b ∧ j=a)
instance (a b i j : ℕ) : Decidable (isPair a b i j) := inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

private theorem orderSign_swap (k i j : ℕ) :
    orderSign (swapIndex k i) (swapIndex k j) =
      if isPair k (k+1) i j then -orderSign i j else orderSign i j := by
  unfold orderSign swapIndex isPair
  split_ifs <;> simp_all <;> (try split_ifs) <;> norm_num <;> omega

/-- The actual color-word tournament matrix D T D on labels less than w.length. -/
def colorGraph (w : List Bool) (i j : ℕ) : ℝ :=
  colorR w i * colorR w j * orderSign i j

/-- All off-diagonal entries are ±1, the diagonal is zero, and the matrix is skew. -/
theorem colorGraph_tournament (w : List Bool) :
    (∀ i, colorGraph w i i = 0) ∧
    (∀ i j, colorGraph w i j = -colorGraph w j i) ∧
    (∀ i j, i ≠ j → (colorGraph w i j)^2 = 1) := by
  have hc (i : ℕ) : (colorR w i)^2=1 := by unfold colorR color; split <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro i; simp [colorGraph, orderSign]
  · intro i j
    unfold colorGraph orderSign
    split_ifs <;> ring_nf; omega
  · intro i j hij
    unfold colorGraph orderSign
    split_ifs <;> simp only [mul_pow, hc] <;> norm_num; omega

/-- After the ordinary label interchange, an adjacent color exchange reverses
exactly the mutual edge and leaves every other matrix entry unchanged. -/
theorem adjacent_matrix_flip (pre tail : List Bool) (a b : Bool) (i j : ℕ) :
    colorGraph (pre ++ b::a::tail) (swapIndex pre.length i) (swapIndex pre.length j) =
      if isPair pre.length (pre.length+1) i j then
        -colorGraph (pre ++ a::b::tail) i j else colorGraph (pre ++ a::b::tail) i j := by
  unfold colorGraph colorR
  rw [adjacent_get, adjacent_get, orderSign_swap]
  split_ifs <;> ring

/-- The designated pair really changes, rather than merely being allowed to change. -/
theorem adjacent_matrix_flip_changes (pre tail : List Bool) (a b : Bool) :
    colorGraph (pre ++ b::a::tail) (swapIndex pre.length pre.length)
        (swapIndex pre.length (pre.length+1)) ≠
      colorGraph (pre ++ a::b::tail) pre.length (pre.length+1) := by
  have hm := adjacent_matrix_flip pre tail a b pre.length (pre.length+1)
  have hs := (colorGraph_tournament (pre ++ a::b::tail)).2.2 pre.length (pre.length+1) (by omega)
  simp only [isPair, true_and, true_or, ite_true] at hm
  intro he
  rw [he] at hm
  nlinarith

/-- A concrete one-edge reversal, allowing only an ordinary permutation of
finite vertex labels, never switching signs of arbitrary vertex neighborhoods. -/
def RelabeledEdgeFlip (N : ℕ) (B C : ℕ → ℕ → ℝ) : Prop :=
  ∃ (e : Equiv ℕ ℕ) (a b : ℕ), a < N ∧ b < N ∧ a ≠ b ∧
    (∀ i, e i < N ↔ i < N) ∧
    ∀ i j, i < N → j < N →
      C (e i) (e j) = if isPair a b i j then -B i j else B i j

/-- Paths of actual one-edge reversals up to ordinary relabeling. -/
inductive GraphEdits (N : ℕ) : ℕ → (ℕ → ℕ → ℝ) → (ℕ → ℕ → ℝ) → Prop
  | refl (B) : GraphEdits N 0 B B
  | edge {B C} : RelabeledEdgeFlip N B C → GraphEdits N 1 B C
  | trans {m n B C D} : GraphEdits N m B C → GraphEdits N n C D → GraphEdits N (m+n) B D

private theorem adjacent_graph_edit (pre tail : List Bool) (a b : Bool) :
    GraphEdits (pre ++ a::b::tail).length 1
      (colorGraph (pre ++ a::b::tail)) (colorGraph (pre ++ b::a::tail)) := by
  apply GraphEdits.edge
  refine ⟨swapEquiv pre.length, pre.length, pre.length+1, ?_, ?_, by omega, ?_, ?_⟩
  · simp
  · simp
  · intro i
    exact swapIndex_bound _ _ i (by simp)
  · intro i j _ _
    exact adjacent_matrix_flip pre tail a b i j

/-- Convert every counted color-swap derivation, under any fixed prefix,
into a counted actual graph-edit path. -/
theorem swaps_graph_edits {n u v} (h : Swaps n u v) (pre : List Bool) :
    GraphEdits (pre ++ u).length n (colorGraph (pre ++ u)) (colorGraph (pre ++ v)) := by
  induction h generalizing pre with
  | refl u => exact GraphEdits.refl _
  | swap a b tail _ => exact adjacent_graph_edit pre tail a b
  | cons a h ih => simpa [List.append_assoc] using ih (pre ++ [a])
  | @trans m n u v w h₁ h₂ ih₁ ih₂ =>
    have he : (pre ++ u).length = (pre ++ v).length := by simp [h₁.perm.length_eq]
    exact GraphEdits.trans (ih₁ pre) (he ▸ ih₂ pre)

/-- The odd energy bound now certifies an actual graph-edit path. -/
theorem odd_graph_repair (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k+1) (hc : charge w = 1) :
    ∃ n, GraphEdits w.length n (colorGraph w) (colorGraph (alternatingOdd k)) ∧
      (n : ℝ) ≤ wordEnergy w / 8 := by
  obtain ⟨n, hn, hb⟩ := odd_energy_repair w k hl hc
  exact ⟨n, by simpa using swaps_graph_edits hn [], hb⟩

/-- The even excess bound now certifies an actual graph-edit path to a paired word. -/
theorem even_graph_repair (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k) (hc : charge w = 0) :
    ∃ n, GraphEdits w.length n (colorGraph w)
      (colorGraph (paired (repairOrient w k))) ∧
      (n : ℝ) ≤ (wordEnergy w - w.length) / 16 := by
  obtain ⟨n, hn, hb⟩ := even_energy_repair w k hl hc
  exact ⟨n, by simpa using swaps_graph_edits hn [], hb⟩

private theorem ordered_row_sum (c : ℕ → ℝ) (n i : ℕ) (hi : i < n) :
    (∑ j ∈ Finset.range n, c i * c j * orderSign i j) =
      c i * ((∑ j ∈ Finset.range n, c j) - 2*(∑ j ∈ Finset.range i, c j) - c i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hin : i < n
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, ih hin]
      have hs : orderSign i n = 1 := by simp [orderSign, hin]
      rw [hs]
      ring
    · have he : i = n := by omega
      subst i
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hs : (∑ j ∈ Finset.range n, c n * c j * orderSign n j) =
          -c n * ∑ j ∈ Finset.range n, c j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hnj : ¬n < j := by omega
        simp [orderSign, hj', hnj]
      rw [hs]
      simp only [orderSign, lt_self_iff_false, ↓reduceIte, mul_zero, add_zero]
      ring

private theorem actual_prefix_step (w : List Bool) (i : ℕ) (hi : i < w.length) :
    prefixR w (i+1) = prefixR w i + colorR w i := by
  have h : charge (w.take (i+1)) = charge (w.take i) + color (w.getD i false) := by
    rw [List.take_succ_eq_append_getElem hi]
    simp only [charge_eq_sum, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    congr 1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  unfold prefixR colorR
  exact_mod_cast h

private theorem actual_prefix_sum (w : List Bool) (i : ℕ) (hi : i ≤ w.length) :
    (∑ j ∈ Finset.range i, colorR w j) = prefixR w i := by
  induction i with
  | zero => simp [prefixR, charge]
  | succ i ih =>
    rw [Finset.sum_range_succ, ih (by omega), actual_prefix_step w i (by omega)]

/-- Actual row sums of D T D equal the color-prefix formula. -/
theorem colorGraph_row_sum (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (∑ j ∈ Finset.range w.length, colorGraph w i j) =
      colorR w i * ((charge w : ℝ) - 2*prefixR w i - colorR w i) := by
  unfold colorGraph
  rw [ordered_row_sum _ _ _ hi, actual_prefix_sum w w.length (by omega),
    actual_prefix_sum w i (by omega)]
  simp [prefixR]

/-- The finite tournament matrix's squared row-sum energy. -/
def graphEnergy (N : ℕ) (B : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, (∑ j ∈ Finset.range N, B i j)^2

/-- The previously verified color energy is literally the matrix row-score energy. -/
theorem graphEnergy_eq_wordEnergy (w : List Bool) :
    graphEnergy w.length (colorGraph w) = wordEnergy w := by
  unfold graphEnergy wordEnergy ColorEnergy.energy
  apply Finset.sum_congr rfl
  intro i hi
  rw [colorGraph_row_sum w i (Finset.mem_range.mp hi), mul_pow]
  have hc : (colorR w i)^2 = 1 := by unfold colorR color; split <;> norm_num
  rw [hc, one_mul]

/-- Odd repair entirely in actual tournament-matrix energy units. -/
theorem odd_matrix_energy_repair (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k+1) (hc : charge w = 1) :
    ∃ n, GraphEdits w.length n (colorGraph w) (colorGraph (alternatingOdd k)) ∧
      (n : ℝ) ≤ graphEnergy w.length (colorGraph w) / 8 := by
  rw [graphEnergy_eq_wordEnergy]
  exact odd_graph_repair w k hl hc

/-- Even repair entirely in actual tournament-matrix excess-energy units. -/
theorem even_matrix_energy_repair (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k) (hc : charge w = 0) :
    ∃ n, GraphEdits w.length n (colorGraph w)
      (colorGraph (paired (repairOrient w k))) ∧
      (n : ℝ) ≤ (graphEnergy w.length (colorGraph w) - w.length) / 16 := by
  rw [graphEnergy_eq_wordEnergy]
  exact even_graph_repair w k hl hc

/-- A finite list of undirected exceptional edges; repetitions are allowed. -/
def edgeCover (es : List (ℕ × ℕ)) (i j : ℕ) : Prop :=
  ∃ p ∈ es, isPair p.1 p.2 i j

private theorem pair_preimage (e : Equiv ℕ ℕ) (a b i j : ℕ) :
    isPair a b (e i) (e j) ↔ isPair (e.symm a) (e.symm b) i j := by
  simp only [isPair, ← Equiv.eq_symm_apply]

/-- Collapse all intermediate relabelings into one final ordinary permutation.
Every discrepancy is covered by an explicit list of exactly n valid edges,
so there are at most n distinct differing undirected edges. -/
theorem graph_edits_certificate {N n B C} (h : GraphEdits N n B C) :
    ∃ (e : Equiv ℕ ℕ) (es : List (ℕ × ℕ)), es.length = n ∧
      (∀ i, e i < N ↔ i < N) ∧
      (∀ p ∈ es, p.1 < N ∧ p.2 < N ∧ p.1 ≠ p.2) ∧
      ∀ i j, i < N → j < N → ¬edgeCover es i j → C (e i) (e j) = B i j := by
  induction h with
  | refl B =>
    refine ⟨Equiv.refl ℕ, [], rfl, ?_, ?_, ?_⟩
    · intro i; rfl
    · simp
    · intro i j _ _ _; rfl
  | @edge B C h =>
    obtain ⟨e, a, b, ha, hb, hab, he, hm⟩ := h
    refine ⟨e, [(a,b)], rfl, he, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      exact ⟨ha, hb, hab⟩
    · intro i j hi hj hnot
      have hn : ¬isPair a b i j := by
        intro hx
        exact hnot ⟨(a,b), by simp, hx⟩
      simpa [hn] using hm i j hi hj
  | @trans m n B C D h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e, es, hlen, he, hvalid, hm⟩ := ih₁
    obtain ⟨f, fs, hlen', hf, hvalid', hm'⟩ := ih₂
    let pull : ℕ × ℕ → ℕ × ℕ := fun p => (e.symm p.1, e.symm p.2)
    refine ⟨e.trans f, es ++ fs.map pull, ?_, ?_, ?_, ?_⟩
    · simp [hlen, hlen']
    · intro i
      exact (hf (e i)).trans (he i)
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hvalid p hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        obtain ⟨hq₁, hq₂, hq₃⟩ := hvalid' q hq
        refine ⟨?_, ?_, ?_⟩
        · have hh := (he (e.symm q.1)).mp
          exact hh (by simpa using hq₁)
        · have hh := (he (e.symm q.2)).mp
          exact hh (by simpa using hq₂)
        · exact fun hh => hq₃ (e.symm.injective hh)
    · intro i j hi hj hnot
      have hn₁ : ¬edgeCover es i j := by
        rintro ⟨p, hp, hx⟩
        exact hnot ⟨p, List.mem_append.mpr (Or.inl hp), hx⟩
      have hn₂ : ¬edgeCover fs (e i) (e j) := by
        rintro ⟨p, hp, hx⟩
        apply hnot
        refine ⟨pull p, List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩)), ?_⟩
        exact (pair_preimage e p.1 p.2 i j).mp hx
      change D (f (e i)) (f (e j)) = B i j
      rw [hm' (e i) (e j) ((he i).mpr hi) ((he j).mpr hj) hn₂]
      exact hm i j hi hj hn₁

/-- A standard final-label discrepancy certificate for odd graph repair. -/
theorem odd_graph_edit_bound (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k+1) (hc : charge w = 1) :
    ∃ (e : Equiv ℕ ℕ) (es : List (ℕ × ℕ)),
      (es.length : ℝ) ≤ graphEnergy w.length (colorGraph w) / 8 ∧
      (∀ i, e i < w.length ↔ i < w.length) ∧
      (∀ p ∈ es, p.1 < w.length ∧ p.2 < w.length ∧ p.1 ≠ p.2) ∧
      ∀ i j, i < w.length → j < w.length → ¬edgeCover es i j →
        colorGraph (alternatingOdd k) (e i) (e j) = colorGraph w i j := by
  obtain ⟨n, hn, hb⟩ := odd_matrix_energy_repair w k hl hc
  obtain ⟨e, es, he, hbound, hvalid, hsame⟩ := graph_edits_certificate hn
  exact ⟨e, es, by simpa [he] using hb, hbound, hvalid, hsame⟩

/-- A standard final-label discrepancy certificate for even graph repair. -/
theorem even_graph_edit_bound (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k) (hc : charge w = 0) :
    ∃ (e : Equiv ℕ ℕ) (es : List (ℕ × ℕ)),
      (es.length : ℝ) ≤ (graphEnergy w.length (colorGraph w) - w.length) / 16 ∧
      (∀ i, e i < w.length ↔ i < w.length) ∧
      (∀ p ∈ es, p.1 < w.length ∧ p.2 < w.length ∧ p.1 ≠ p.2) ∧
      ∀ i j, i < w.length → j < w.length → ¬edgeCover es i j →
        colorGraph (paired (repairOrient w k)) (e i) (e j) = colorGraph w i j := by
  obtain ⟨n, hn, hb⟩ := even_matrix_energy_repair w k hl hc
  obtain ⟨e, es, he, hbound, hvalid, hsame⟩ := graph_edits_certificate hn
  exact ⟨e, es, by simpa [he] using hb, hbound, hvalid, hsame⟩

/-- Distinct undirected differing edges after a single ordinary relabeling.
Only i<j is counted, so each edge contributes once. -/
noncomputable def mismatchEdges (N : ℕ) (B C : ℕ → ℕ → ℝ) (e : Equiv ℕ ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range N).product (Finset.range N)).filter
    (fun p => p.1 < p.2 ∧ C (e p.1) (e p.2) ≠ B p.1 p.2)

private def orderedEdge (p : ℕ × ℕ) : ℕ × ℕ := (min p.1 p.2, max p.1 p.2)

/-- An edge-cover certificate bounds the usual number of differing graph edges. -/
theorem mismatch_card_le {N B C e} (es : List (ℕ × ℕ))
    (hsame : ∀ i j, i < N → j < N → ¬edgeCover es i j → C (e i) (e j) = B i j) :
    (mismatchEdges N B C e).card ≤ es.length := by
  classical
  have hsub : mismatchEdges N B C e ⊆ es.toFinset.image orderedEdge := by
    intro p hp
    obtain ⟨hmem, hporder, hpneq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hmem
    have hcover : edgeCover es p.1 p.2 := by
      by_contra hn
      exact hpneq (hsame p.1 p.2 (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hn)
    obtain ⟨q, hq, hpair⟩ := hcover
    refine Finset.mem_image.mpr ⟨q, by simpa using hq, ?_⟩
    rcases p with ⟨i,j⟩
    rcases q with ⟨a,b⟩
    rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp [orderedEdge, min_eq_left (Nat.le_of_lt hporder), max_eq_right (Nat.le_of_lt hporder)]
    · simp [orderedEdge, min_eq_right (Nat.le_of_lt hporder), max_eq_left (Nat.le_of_lt hporder)]
  calc
    (mismatchEdges N B C e).card ≤ (es.toFinset.image orderedEdge).card := Finset.card_le_card hsub
    _ ≤ es.toFinset.card := Finset.card_image_le
    _ ≤ es.length := List.toFinset_card_le es

/-- The ordinary final-label graph edit upper bound E/8. -/
theorem odd_edit_card_bound (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k+1) (hc : charge w = 1) :
    ∃ e : Equiv ℕ ℕ, (∀ i, e i < w.length ↔ i < w.length) ∧
      ((mismatchEdges w.length (colorGraph w) (colorGraph (alternatingOdd k)) e).card : ℝ) ≤
        graphEnergy w.length (colorGraph w) / 8 := by
  obtain ⟨e, es, hb, he, _, hsame⟩ := odd_graph_edit_bound w k hl hc
  refine ⟨e, he, ?_⟩
  have h : ((mismatchEdges w.length (colorGraph w) (colorGraph (alternatingOdd k)) e).card : ℝ) ≤
      es.length := by exact_mod_cast mismatch_card_le es hsame
  exact h.trans hb

/-- The ordinary final-label graph edit upper bound (E-m)/16. -/
theorem even_edit_card_bound (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k) (hc : charge w = 0) :
    ∃ e : Equiv ℕ ℕ, (∀ i, e i < w.length ↔ i < w.length) ∧
      ((mismatchEdges w.length (colorGraph w) (colorGraph (paired (repairOrient w k))) e).card : ℝ) ≤
        (graphEnergy w.length (colorGraph w) - w.length) / 16 := by
  obtain ⟨e, es, hb, he, _, hsame⟩ := even_graph_edit_bound w k hl hc
  refine ⟨e, he, ?_⟩
  have h : ((mismatchEdges w.length (colorGraph w) (colorGraph (paired (repairOrient w k))) e).card : ℝ) ≤
      es.length := by exact_mod_cast mismatch_card_le es hsame
  exact h.trans hb

#print axioms mismatch_card_le
#print axioms odd_edit_card_bound
#print axioms even_edit_card_bound
#print axioms graph_edits_certificate
#print axioms odd_graph_edit_bound
#print axioms even_graph_edit_bound
#print axioms colorGraph_tournament
#print axioms colorGraph_row_sum
#print axioms graphEnergy_eq_wordEnergy
#print axioms odd_matrix_energy_repair
#print axioms even_matrix_energy_repair
#print axioms adjacent_matrix_flip_changes
#print axioms adjacent_matrix_flip
#print axioms swaps_graph_edits
#print axioms odd_graph_repair
#print axioms even_graph_repair
end ColorTransport
