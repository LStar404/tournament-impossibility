import TournamentSourceEnergy
noncomputable section
namespace StrongTournamentTriangles
open Finset VectorWeakMajorization

/-- Actual directed-path strong connectivity, including length-zero paths. -/
def Strong {n : ℕ} (B : Tournament n) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun x y => B.entry x y = 1) i j

lemma strong_cut {n : ℕ} (B : Tournament n) (hB : Strong B)
    (s : Finset (Fin n)) (hs : s.Nonempty) (hp : ∃ j, j ∉ s) :
    ∃ i ∈ s, ∃ j ∉ s, B.entry i j = 1 := by
  classical
  by_contra hn
  have hc : ∀ i ∈ s, ∀ j, B.entry i j = 1 → j ∈ s := by
    intro i hi j hij
    by_contra hj
    exact hn ⟨i,hi,j,hj,hij⟩
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj⟩ := hp
  have hpath := hB i j
  have hm : j ∈ s := by
    clear hj
    induction hpath with
    | refl => exact hi
    | @tail b c hab hbc ih => exact hc b ih c hbc
  exact hj hm

/-- Every vertex of a nontrivial strongly connected actual tournament belongs
 to a directed 3-cycle. No cycle-count bound is assumed. -/
theorem vertex_triangle {n : ℕ} (B : Tournament n) (hB : Strong B)
    (hn : 2 ≤ n) (v : Fin n) :
    ∃ i j, B.entry v i = 1 ∧ B.entry i j = 1 ∧ B.entry j v = 1 := by
  classical
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨a, ha, b, hb, hab⟩ := strong_cut B hB {v} (by simp) ⟨w,by simpa using hw⟩
  have hav : a=v := by simpa using ha
  subst a
  let s : Finset (Fin n) := univ.filter (fun i => B.entry v i = 1)
  have hs : s.Nonempty := ⟨b,by simp [s,hab]⟩
  have hv : v ∉ s := by simp [s, B.diagonal v]
  obtain ⟨i,hi,j,hj,hij⟩ := strong_cut B hB s hs ⟨v,hv⟩
  have hvi : B.entry v i = 1 := (mem_filter.mp hi).2
  have hjv : j ≠ v := by
    intro he
    subst j
    have h := B.skew i v
    linarith
  have hvj : B.entry v j ≠ 1 := by
    intro he
    exact hj (by simp [s,he])
  rcases B.unit j v hjv with hjpos | hjneg
  · exact ⟨i,j,hvi,hij,hjpos⟩
  · have h := B.skew v j
    exact (hvj (by linarith)).elim

/-- The genuine ordered cycle count bounds the number of vertices. Since each
cyclic three-set has three positive orientations, this is the m≤3t bound. -/
theorem card_le_cycleCount {n : ℕ} (B : Tournament n) (hB : Strong B)
    (hn : 2 ≤ n) : n ≤ TournamentSourceEnergy.cycleCount B := by
  classical
  choose i j hij using vertex_triangle B hB hn
  let f : Fin n → Fin n × Fin n × Fin n := fun v => (v,i v,j v)
  have hmap : Set.MapsTo f (univ : Finset (Fin n))
      (univ.filter fun t : Fin n × Fin n × Fin n =>
        B.entry t.1 t.2.1 = 1 ∧ B.entry t.2.1 t.2.2 = 1 ∧ B.entry t.2.2 t.1 = 1) := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _, hij v⟩
  have hinj : (↑(univ : Finset (Fin n)) : Set (Fin n)).InjOn f := by
    intro v hv w hw he
    exact congrArg Prod.fst he
  have h := card_le_card_of_injOn f hmap hinj
  simpa only [card_univ, Fintype.card_fin, TournamentSourceEnergy.cycleCount] using h

/-- Source-normalized real form, with a real count rather than Nat division. -/
theorem size_le_three_triangles {n : ℕ} (B : Tournament n) (hB : Strong B)
    (hn : 2 ≤ n) : (n : ℝ) ≤ 3*((TournamentSourceEnergy.cycleCount B : ℝ)/3) := by
  have h := card_le_cycleCount B hB hn
  have hr : (n : ℝ) ≤ (TournamentSourceEnergy.cycleCount B : ℝ) := by exact_mod_cast h
  linarith

lemma size_le_max_cycleCount {n : ℕ} (B : Tournament n) (hB : Strong B) :
    n ≤ max 1 (TournamentSourceEnergy.cycleCount B) := by
  by_cases hn : 2 ≤ n
  · exact le_trans (card_le_cycleCount B hB hn) (le_max_right _ _)
  · have hn1 : n ≤ 1 := by omega
    exact le_trans hn1 (le_max_left _ _)

/-- Strong blocks of an actual family are bounded by its total directed-cycle
count as soon as that total is positive. No SCC decomposition is asserted. -/
theorem block_size_le_total (m : ℕ → ℕ) (B : ∀ i, Tournament (m i)) (k : ℕ)
    (hB : ∀ i ∈ range k, Strong (B i))
    (hpos : 0 < ∑ i ∈ range k, TournamentSourceEnergy.cycleCount (B i))
    (i : ℕ) (hi : i ∈ range k) :
    m i ≤ ∑ j ∈ range k, TournamentSourceEnergy.cycleCount (B j) := by
  have hlocal := size_le_max_cycleCount (B i) (hB i hi)
  have hcount : TournamentSourceEnergy.cycleCount (B i) ≤
      ∑ j ∈ range k, TournamentSourceEnergy.cycleCount (B j) :=
    single_le_sum (f := fun j => TournamentSourceEnergy.cycleCount (B j)) (fun j hj => Nat.zero_le _) hi
  exact le_trans hlocal (max_le (by omega) hcount)

/-- Conditional numerical consequence of the actual strong-block count bound.
The averaging inequality is explicit and must come from the pivot-link theorem. -/
theorem block_size_from_link (m : ℕ → ℕ) (B : ∀ i, Tournament (m i))
    (k : ℕ) (n D : ℝ) (hn : 0 < n)
    (hB : ∀ i ∈ range k, Strong (B i))
    (hpos : 0 < ∑ i ∈ range k, TournamentSourceEnergy.cycleCount (B i))
    (hlink : n*((∑ i ∈ range k, (TournamentSourceEnergy.cycleCount (B i) : ℝ))/3) ≤ 4*D)
    (i : ℕ) (hi : i ∈ range k) : (m i : ℝ) ≤ 12*D/n := by
  have hs := block_size_le_total m B k hB hpos i hi
  have hsr : (m i : ℝ) ≤ ∑ j ∈ range k, (TournamentSourceEnergy.cycleCount (B j) : ℝ) := by
    exact_mod_cast hs
  apply (le_div_iff₀ hn).mpr
  have hm := mul_le_mul_of_nonneg_left hsr (le_of_lt hn)
  nlinarith
end StrongTournamentTriangles
#print axioms StrongTournamentTriangles.vertex_triangle
#print axioms StrongTournamentTriangles.card_le_cycleCount
