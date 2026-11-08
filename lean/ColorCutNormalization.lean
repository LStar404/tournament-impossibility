import ColorGraphRepair
namespace ColorTransport

private theorem color_not (a : Bool) : color (!a) = -color a := by cases a <;> decide

private theorem charge_append (u v : List Bool) : charge (u++v) = charge u + charge v := by
  simp [charge_eq_sum]

private theorem charge_not (u : List Bool) : charge (u.map Bool.not) = -charge u := by
  induction u with
  | nil => simp [charge]
  | cons a u ih => simp only [List.map_cons, charge_cons, color_not, ih]; ring

/-- Rotate the first k colors to the end and negate just those moved colors. -/
def cutWord (w : List Bool) (k : ℕ) : List Bool := w.drop k ++ (w.take k).map Bool.not

@[simp] theorem cutWord_length (w : List Bool) (k : ℕ) : (cutWord w k).length = w.length := by
  simp [cutWord]
  omega

/-- The exact total-color change induced by a cut. -/
theorem cutWord_charge (w : List Bool) (k : ℕ) :
    charge (cutWord w k) = charge w - 2*charge (w.take k) := by
  have h : charge (w.take k) + charge (w.drop k) = charge w := by
    rw [← charge_append, List.take_append_drop]
  rw [cutWord, charge_append, charge_not]
  omega

/-- A finite ±1 word hits every integer between zero and its final charge. -/
theorem charge_prefix_ivt (w : List Bool) (t : ℤ)
    (ht : (0 ≤ t ∧ t ≤ charge w) ∨ (charge w ≤ t ∧ t ≤ 0)) :
    ∃ k, k ≤ w.length ∧ charge (w.take k) = t := by
  induction w generalizing t with
  | nil =>
    have he : t = 0 := by simp [charge] at ht; omega
    exact ⟨0, by simp, by simp [charge, he]⟩
  | cons a w ih =>
    by_cases hz : t = 0
    · exact ⟨0, by simp, by simp [charge, hz]⟩
    · have hs : (0 ≤ t-color a ∧ t-color a ≤ charge w) ∨
          (charge w ≤ t-color a ∧ t-color a ≤ 0) := by
        rw [charge_cons] at ht
        cases a <;> simp only [color, Bool.false_eq_true, ↓reduceIte] at * <;> omega
      obtain ⟨k, hk, he⟩ := ih (t-color a) hs
      refine ⟨k+1, by simpa using hk, ?_⟩
      simp only [List.take_succ_cons, charge_cons]
      omega

/-- Every color word has a cut with total 0 or 1, without an unproved
continuous intermediate-value or monotonicity assumption. -/
theorem normalized_cut_exists (w : List Bool) :
    ∃ k, k ≤ w.length ∧ charge (cutWord w k) = charge w % 2 := by
  have ht : (0 ≤ charge w / 2 ∧ charge w / 2 ≤ charge w) ∨
      (charge w ≤ charge w / 2 ∧ charge w / 2 ≤ 0) := by omega
  obtain ⟨k, hk, he⟩ := charge_prefix_ivt w (charge w / 2) ht
  refine ⟨k, hk, ?_⟩
  rw [cutWord_charge, he]
  omega

/-- The normal form's total is the parity of the vertex count. -/
theorem normalized_cut_parity (w : List Bool) :
    ∃ k, k ≤ w.length ∧ charge (cutWord w k) = (w.length%2 : ℕ) := by
  obtain ⟨k, hk, he⟩ := normalized_cut_exists w
  refine ⟨k, hk, ?_⟩
  have hs := counts_sum_length w
  unfold charge at he ⊢
  omega

/-- Exchange blocks of lengths a,b, leaving all outside labels fixed. -/
def rotateIndex (a b i : ℕ) : ℕ :=
  if i < a then b+i else if i < a+b then i-a else i

private theorem rotateIndex_inverse (a b i : ℕ) :
    rotateIndex b a (rotateIndex a b i) = i := by
  unfold rotateIndex
  split_ifs <;> omega

def rotateEquiv (a b : ℕ) : Equiv ℕ ℕ where
  toFun := rotateIndex a b
  invFun := rotateIndex b a
  left_inv := rotateIndex_inverse a b
  right_inv := rotateIndex_inverse b a

private theorem rotateIndex_bound (a b i : ℕ) :
    rotateIndex a b i < a+b ↔ i < a+b := by
  unfold rotateIndex
  split_ifs <;> omega

private theorem rotated_color (u v : List Bool) (i : ℕ) (hi : i < u.length+v.length) :
    colorR (v ++ u.map Bool.not) (rotateIndex u.length v.length i) =
      if i < u.length then -colorR (u++v) i else colorR (u++v) i := by
  unfold colorR rotateIndex
  by_cases h : i < u.length
  · simp only [h, ↓reduceIte]
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : v.length ≤ v.length+i),
      Nat.add_sub_cancel_left, List.getElem?_map,
      List.getElem?_append_left h, List.getElem?_eq_getElem h, Option.map_some,
      Option.getD_some, color_not, Int.cast_neg]
  · simp only [h, hi, ↓reduceIte]
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega : i-u.length < v.length),
      List.getElem?_append_right (by omega : u.length ≤ i)]

/-- Moving a prefix to the end and negating it preserves the actual graph
by an ordinary vertex permutation; this is not arbitrary sign switching. -/
theorem cut_blocks_isomorphic (u v : List Bool) (i j : ℕ)
    (hi : i < u.length+v.length) (hj : j < u.length+v.length) :
    colorGraph (v ++ u.map Bool.not) (rotateIndex u.length v.length i)
        (rotateIndex u.length v.length j) = colorGraph (u++v) i j := by
  unfold colorGraph
  rw [rotated_color u v i hi, rotated_color u v j hj]
  unfold rotateIndex orderSign
  split_ifs <;> ring_nf <;> try omega

/-- A normalized representative and a single ordinary finite-vertex isomorphism
for every word in the color-word class. No arbitrary tournament representation
claim is made. -/
theorem normalized_graph_exists (w : List Bool) :
    ∃ (v : List Bool) (e : Equiv ℕ ℕ), v.length = w.length ∧
      charge v = (w.length%2 : ℕ) ∧
      (∀ i, e i < w.length ↔ i < w.length) ∧
      ∀ i j, i < w.length → j < w.length → colorGraph v (e i) (e j) = colorGraph w i j := by
  obtain ⟨k, hk, hc⟩ := normalized_cut_parity w
  refine ⟨cutWord w k, rotateEquiv (w.take k).length (w.drop k).length,
    cutWord_length w k, hc, ?_, ?_⟩
  · intro i
    have hs : (w.take k).length + (w.drop k).length = w.length := by simp; omega
    have hb := rotateIndex_bound (w.take k).length (w.drop k).length i
    rw [hs] at hb
    exact hb
  · intro i j hi hj
    have hs : (w.take k).length + (w.drop k).length = w.length := by simp; omega
    have hm := cut_blocks_isomorphic (w.take k) (w.drop k) i j (by omega) (by omega)
    simpa [cutWord, rotateEquiv, List.take_append_drop] using hm

/-- Finite sums are unchanged by an ordinary permutation preserving the vertex set. -/
theorem sum_range_equiv (N : ℕ) (e : Equiv ℕ ℕ)
    (he : ∀ i, e i < N ↔ i < N) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, f (e i)) = ∑ i ∈ Finset.range N, f i := by
  apply Finset.sum_bij (fun i _ => e i)
  · intro i hi
    exact Finset.mem_range.mpr ((he i).mpr (Finset.mem_range.mp hi))
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, ?_, by simp⟩
    apply Finset.mem_range.mpr
    have h := (he (e.symm j)).mp
    apply h
    simpa using Finset.mem_range.mp hj
  · intro i _; rfl

/-- Actual squared row-sum energy is invariant under ordinary finite-vertex isomorphism. -/
theorem graphEnergy_isomorphism (N : ℕ) (B C : ℕ → ℕ → ℝ)
    (e : Equiv ℕ ℕ) (he : ∀ i, e i < N ↔ i < N)
    (hm : ∀ i j, i < N → j < N → C (e i) (e j) = B i j) :
    graphEnergy N B = graphEnergy N C := by
  unfold graphEnergy
  rw [← sum_range_equiv N e he (fun i => (∑ j ∈ Finset.range N, C i j)^2)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sum_range_equiv N e he (fun j => C (e i) j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact (hm i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)).symm

/-- Every color-word graph admits a normalized representative of the same
actual matrix energy, by an explicitly certified ordinary isomorphism. -/
theorem normalized_graph_energy_exists (w : List Bool) :
    ∃ (v : List Bool) (e : Equiv ℕ ℕ), v.length = w.length ∧
      charge v = (w.length%2 : ℕ) ∧ wordEnergy v = wordEnergy w ∧
      (∀ i, e i < w.length ↔ i < w.length) ∧
      ∀ i j, i < w.length → j < w.length → colorGraph v (e i) (e j) = colorGraph w i j := by
  obtain ⟨v, e, hl, hc, he, hm⟩ := normalized_graph_exists w
  refine ⟨v, e, hl, hc, ?_, he, hm⟩
  have hh := graphEnergy_isomorphism w.length (colorGraph w) (colorGraph v) e he hm
  rw [graphEnergy_eq_wordEnergy w, ← hl, graphEnergy_eq_wordEnergy v] at hh
  exact hh.symm

/-- Pull back a genuine edge cover through the initial ordinary isomorphism. -/
theorem mismatch_card_pullback (N : ℕ) (B C D : ℕ → ℕ → ℝ)
    (e f : Equiv ℕ ℕ) (es : List (ℕ × ℕ))
    (he : ∀ i, e i < N ↔ i < N)
    (hm : ∀ i j, i < N → j < N → C (e i) (e j) = B i j)
    (ht : ∀ i j, i < N → j < N → ¬edgeCover es i j → D (f i) (f j) = C i j) :
    (mismatchEdges N B D (e.trans f)).card ≤ es.length := by
  let pull : ℕ × ℕ → ℕ × ℕ := fun p => (e.symm p.1, e.symm p.2)
  have hs : ∀ i j, i < N → j < N → ¬edgeCover (es.map pull) i j →
      D ((e.trans f) i) ((e.trans f) j) = B i j := by
    intro i j hi hj hn
    have hn' : ¬edgeCover es (e i) (e j) := by
      rintro ⟨p, hp, hx⟩
      apply hn
      refine ⟨pull p, List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
      simpa only [pull, isPair, ← Equiv.eq_symm_apply] using hx
    change D (f (e i)) (f (e j)) = B i j
    rw [ht (e i) (e j) ((he i).mpr hi) ((he j).mpr hj) hn']
    exact hm i j hi hj
  simpa using mismatch_card_le (es.map pull) hs

/-- Odd graph-edit bound for every color word, with no normalized-total
hypothesis remaining. This is still only the color-word graph class. -/
theorem arbitrary_odd_word_repair (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k+1) :
    ∃ e : Equiv ℕ ℕ, (∀ i, e i < w.length ↔ i < w.length) ∧
      ((mismatchEdges w.length (colorGraph w) (colorGraph (alternatingOdd k)) e).card : ℝ) ≤
        graphEnergy w.length (colorGraph w) / 8 := by
  obtain ⟨v, e, hv, hc, he, hm⟩ := normalized_graph_exists w
  have hcv : charge v = 1 := by rw [hl] at hc; simpa using hc
  have hlv : v.length = 2*k+1 := hv.trans hl
  obtain ⟨f, es, hb, hf, _, ht⟩ := odd_graph_edit_bound v k hlv hcv
  rw [hv] at hb hf ht
  have henergy := graphEnergy_isomorphism w.length (colorGraph w) (colorGraph v) e he hm
  rw [← henergy] at hb
  refine ⟨e.trans f, fun i => (hf (e i)).trans (he i), ?_⟩
  have hcard : ((mismatchEdges w.length (colorGraph w)
      (colorGraph (alternatingOdd k)) (e.trans f)).card : ℝ) ≤ es.length := by
    exact_mod_cast mismatch_card_pullback w.length _ _ _ e f es he hm ht
  exact hcard.trans hb

/-- Even graph-edit bound for every color word, with an actual paired target
of half the input length. No arbitrary tournament representation is assumed. -/
theorem arbitrary_even_word_repair (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k) :
    ∃ (orient : List Bool) (e : Equiv ℕ ℕ), orient.length = k ∧
      (∀ i, e i < w.length ↔ i < w.length) ∧
      ((mismatchEdges w.length (colorGraph w) (colorGraph (paired orient)) e).card : ℝ) ≤
        (graphEnergy w.length (colorGraph w) - w.length) / 16 := by
  obtain ⟨v, e, hv, hc, he, hm⟩ := normalized_graph_exists w
  have hcv : charge v = 0 := by rw [hl] at hc; simpa using hc
  have hlv : v.length = 2*k := hv.trans hl
  obtain ⟨f, es, hb, hf, _, ht⟩ := even_graph_edit_bound v k hlv hcv
  rw [hv] at hb hf ht
  have henergy := graphEnergy_isomorphism w.length (colorGraph w) (colorGraph v) e he hm
  rw [← henergy] at hb
  refine ⟨repairOrient v k, e.trans f, by simp [repairOrient],
    fun i => (hf (e i)).trans (he i), ?_⟩
  have hcard : ((mismatchEdges w.length (colorGraph w)
      (colorGraph (paired (repairOrient v k))) (e.trans f)).card : ℝ) ≤ es.length := by
    exact_mod_cast mismatch_card_pullback w.length _ _ _ e f es he hm ht
  exact hcard.trans hb

#print axioms arbitrary_odd_word_repair
#print axioms arbitrary_even_word_repair
#print axioms graphEnergy_isomorphism
#print axioms normalized_graph_energy_exists
#print axioms charge_prefix_ivt
#print axioms normalized_cut_parity
#print axioms cut_blocks_isomorphic
#print axioms normalized_graph_exists
end ColorTransport
