import TournamentComponentBlocks
import OrdinalTransitiveReference
import OrdinalTriangleAdditivity
noncomputable section
namespace TournamentOrdinalReconstruction
open Finset Matrix VectorWeakMajorization TournamentComponents OrdinalBlockMatrix
variable {n : ℕ} (B : Tournament n)

def count : ℕ := Fintype.card (Component B)
def rank : Component B ≃o Fin (count B) := (Fintype.orderIsoFinOfCardEq (Component B) rfl).symm
def vertexRank (v : Fin n) : ℕ := ((rank B) (componentOf B v)).val

def RankFiber (k : ℕ) := {v : Fin n // vertexRank B v = k}
instance rankFiberFintype (k : ℕ) : Fintype (RankFiber B k) := by
  classical
  exact inferInstanceAs (Fintype {v : Fin n // vertexRank B v = k})
instance rankFiberDecidableEq (k : ℕ) : DecidableEq (RankFiber B k) := Classical.decEq _

def blockSize (k : ℕ) : ℕ := Fintype.card (RankFiber B k)
def rankEquiv (k : ℕ) : Fin (blockSize B k) ≃ RankFiber B k :=
  (Fintype.equivFin (RankFiber B k)).symm
def rankEmbed (k : ℕ) (i : Fin (blockSize B k)) : Fin n := (rankEquiv B k i).val
lemma rankEmbed_rank (k : ℕ) (i : Fin (blockSize B k)) : vertexRank B (rankEmbed B k i) = k :=
  (rankEquiv B k i).property
lemma rankEmbed_injective (k : ℕ) : Function.Injective (rankEmbed B k) := by
  intro i j h
  apply (rankEquiv B k).injective
  exact Subtype.ext h

def block (k : ℕ) : Tournament (blockSize B k) where
  entry i j := B.entry (rankEmbed B k i) (rankEmbed B k j)
  skew i j := B.skew _ _
  unit i j hij := B.unit _ _ (fun h => hij (rankEmbed_injective B k h))

/-- Rank fibers are exactly the corresponding actual component fibers. -/
def rankFiberComponentEquiv (C : Component B) :
    RankFiber B ((rank B C).val) ≃ TournamentComponentBlocks.Fiber B C where
  toFun v := ⟨v.val, (rank B).injective (Fin.ext v.property)⟩
  invFun v := ⟨v.val, congrArg (fun D : Component B => (rank B D).val) v.property⟩
  left_inv v := Subtype.ext rfl
  right_inv v := Subtype.ext rfl

lemma blockSize_component (C : Component B) :
    blockSize B ((rank B C).val) = TournamentComponentBlocks.size B C :=
  Fintype.card_congr (rankFiberComponentEquiv B C)

lemma block_strong_component (C : Component B) :
    StrongTournamentTriangles.Strong (block B ((rank B C).val)) := by
  let e := (rankEquiv B ((rank B C).val)).trans (rankFiberComponentEquiv B C)
  have hs (u : TournamentComponentBlocks.Fiber B C) :
      rankEmbed B ((rank B C).val) (e.symm u) = u.val :=
    congrArg Subtype.val (e.apply_symm_apply u)
  intro i j
  let a := e i
  let b := e j
  have hab : Reach B a.val b.val :=
    ((component_eq_iff B a.val b.val).mp (a.property.trans b.property.symm)).1
  have hp := TournamentComponentBlocks.path_in_fiber B C a.property b.property hab
  have hh := Relation.ReflTransGen.lift e.symm
    (p := fun u v => (block B ((rank B C).val)).entry u v = 1)
    (by
      intro u v huv
      change B.entry (rankEmbed B ((rank B C).val) (e.symm u))
        (rankEmbed B ((rank B C).val) (e.symm v)) = 1
      rw [hs, hs]
      exact huv) a b hp
  simpa only [Function.onFun, a, b, Equiv.symm_apply_apply] using hh

/-- Every block in the reconstructed finite family is actually strong. -/
theorem block_strong (k : ℕ) (hk : k < count B) :
    StrongTournamentTriangles.Strong (block B k) := by
  let C := (rank B).symm ⟨k,hk⟩
  have hr : (rank B C).val = k := by simp [C]
  have h := block_strong_component B C
  rw [hr] at h
  exact h

lemma blockSize_le_global (k : ℕ) (hk : k < count B)
    (hpos : 0 < TournamentSourceEnergy.cycleCount B) :
    blockSize B k ≤ TournamentSourceEnergy.cycleCount B := by
  let C := (rank B).symm ⟨k,hk⟩
  have hr : (rank B C).val = k := by simp [C]
  calc
    _ = TournamentComponentBlocks.size B C := by rw [← hr]; exact blockSize_component B C
    _ ≤ _ := TournamentComponentBlocks.component_size_le_cycleCount B C hpos

def vertex : (k : ℕ) → Carrier (blockSize B) k → Fin n
  | 0, i => Fin.elim0 i
  | k+1, Sum.inl i => vertex k i
  | k+1, Sum.inr i => rankEmbed B k i

lemma vertex_rank_lt (k : ℕ) (i : Carrier (blockSize B) k) :
    vertexRank B (vertex B k i) < k := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i with
    | inl i => exact Nat.lt_succ_of_lt (ih i)
    | inr i => simpa only [vertex, rankEmbed_rank] using Nat.lt_succ_self k

lemma vertex_injective (k : ℕ) : Function.Injective (vertex B k) := by
  induction k with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (ih h)
      | inr j =>
        have hi := vertex_rank_lt B k i
        have hj := rankEmbed_rank B k j
        have he := congrArg (vertexRank B) h
        change vertexRank B (vertex B k i) = vertexRank B (rankEmbed B k j) at he
        omega
    | inr i =>
      cases j with
      | inl j =>
        have hi := rankEmbed_rank B k i
        have hj := vertex_rank_lt B k j
        have he := congrArg (vertexRank B) h
        change vertexRank B (rankEmbed B k i) = vertexRank B (vertex B k j) at he
        omega
      | inr j => exact congrArg Sum.inr (rankEmbed_injective B k h)

lemma vertex_surjective_upto (k : ℕ) (v : Fin n) (hv : vertexRank B v < k) :
    ∃ i : Carrier (blockSize B) k, vertex B k i = v := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hlt : vertexRank B v < k
    · obtain ⟨i,hi⟩ := ih hlt
      exact ⟨Sum.inl i, hi⟩
    · have he : vertexRank B v = k := by omega
      refine ⟨Sum.inr ((rankEquiv B k).symm ⟨v,he⟩), ?_⟩
      exact congrArg Subtype.val ((rankEquiv B k).apply_symm_apply ⟨v,he⟩)

/-- Canonical ordinal-block carrier is actually bijective with all vertices. -/
def reconstruction : Carrier (blockSize B) (count B) ≃ Fin n :=
  Equiv.ofBijective (vertex B (count B))
    ⟨vertex_injective B (count B), fun v => vertex_surjective_upto B (count B) v
      (((rank B) (componentOf B v)).isLt)⟩

lemma edge_of_rank_lt {v w : Fin n} (h : vertexRank B v < vertexRank B w) : B.entry v w = 1 := by
  have hc : componentOf B v < componentOf B w :=
    (rank B).lt_iff_lt.mp h
  exact ((component_lt_iff B v w).mp hc).1

/-- Exact actual matrix reconstruction, with no block decomposition premise. -/
theorem entry (k : ℕ) (i j : Carrier (blockSize B) k) :
    matrix (blockSize B) (fun a => (block B a).entry) k i j =
      B.entry (vertex B k i) (vertex B k j) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i with
    | inl i =>
      cases j with
      | inl j => exact ih i j
      | inr j =>
        change (1:ℝ) = B.entry (vertex B k i) (rankEmbed B k j)
        exact (edge_of_rank_lt B (by rw [rankEmbed_rank]; exact vertex_rank_lt B k i)).symm
    | inr i =>
      cases j with
      | inl j =>
        change (-1:ℝ) = B.entry (rankEmbed B k i) (vertex B k j)
        have he := edge_of_rank_lt B (show vertexRank B (vertex B k j) < vertexRank B (rankEmbed B k i) by
          rw [rankEmbed_rank]; exact vertex_rank_lt B k j)
        have hs := B.skew (rankEmbed B k i) (vertex B k j)
        linarith
      | inr j => rfl

/-- Total block size is exactly n; no vertices are omitted or duplicated. -/
theorem sum_sizes : (∑ k ∈ range (count B), blockSize B k) = n := by
  have h := Fintype.card_congr (reconstruction B)
  rw [OrdinalBlockMatrix.cardinality, Fintype.card_fin] at h
  exact h

/-- Reconstruction preserves all natural-number-power Frobenius moments. -/
theorem power_frobenius_eq (r : ℕ) :
    (∑ i : Carrier (blockSize B) (count B), ∑ j : Carrier (blockSize B) (count B),
      (((matrix (blockSize B) (fun a => (block B a).entry) (count B))^r) i j)^2) =
      ∑ i : Fin n, ∑ j : Fin n, (((show Matrix (Fin n) (Fin n) ℝ from B.entry)^r) i j)^2 := by
  apply OrdinalTransitiveReference.power_frobenius_relabel (reconstruction B)
  intro i j
  exact entry B (count B) i j

theorem sixth_eq :
    TwoBlockSixthMoment.third (matrix (blockSize B) (fun a => (block B a).entry) (count B)) =
      TwoBlockSixthMoment.third (show Matrix (Fin n) (Fin n) ℝ from B.entry) := by
  simpa only [TwoBlockSixthMoment.third, RectangularFrobenius.sqnorm,
    RectangularFrobenius.inner, pow_two] using power_frobenius_eq B 3
/-- Reindexing the actual directed triangle sum loses no triples. -/
theorem cycleSum_eq :
    OrdinalTriangleAdditivity.cycleSum
      (matrix (blockSize B) (fun a => (block B a).entry) (count B)) =
      OrdinalTriangleAdditivity.cycleSum (TournamentPowerComparison.matrix B) := by
  unfold OrdinalTriangleAdditivity.cycleSum
  let e := reconstruction B
  calc
    _ = ∑ i, ∑ j, ∑ k,
        if B.entry (e i) (e j) = 1 ∧ B.entry (e j) (e k) = 1 ∧
          B.entry (e k) (e i) = 1 then (1 : ℝ) else 0 := by
      apply sum_congr rfl; intro i hi
      apply sum_congr rfl; intro j hj
      apply sum_congr rfl; intro k hk
      simp only [entry]
      rfl
    _ = ∑ i, ∑ j, ∑ k : Fin n,
        if B.entry (e i) (e j) = 1 ∧ B.entry (e j) k = 1 ∧ B.entry k (e i) = 1 then (1 : ℝ) else 0 := by
      apply sum_congr rfl; intro i hi
      apply sum_congr rfl; intro j hj
      exact Equiv.sum_comp e (fun k => if B.entry (e i) (e j) = 1 ∧ B.entry (e j) k = 1 ∧ B.entry k (e i) = 1 then (1 : ℝ) else 0)
    _ = ∑ i, ∑ j : Fin n, ∑ k : Fin n,
        if B.entry (e i) j = 1 ∧ B.entry j k = 1 ∧ B.entry k (e i) = 1 then (1 : ℝ) else 0 := by
      apply sum_congr rfl; intro i hi
      exact Equiv.sum_comp e (fun j => ∑ k : Fin n, if B.entry (e i) j = 1 ∧ B.entry j k = 1 ∧ B.entry k (e i) = 1 then (1 : ℝ) else 0)
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        if B.entry i j = 1 ∧ B.entry j k = 1 ∧ B.entry k i = 1 then (1 : ℝ) else 0 :=
      Equiv.sum_comp e (fun i => ∑ j : Fin n, ∑ k : Fin n, if B.entry i j = 1 ∧ B.entry j k = 1 ∧ B.entry k i = 1 then (1 : ℝ) else 0)
    _ = _ := rfl

/-- The sum of the internal directed triangle counts is the original count. -/
theorem cycleCount_sum :
    (∑ i ∈ range (count B), (TournamentSourceEnergy.cycleCount (block B i) : ℝ)) =
      (TournamentSourceEnergy.cycleCount B : ℝ) := by
  rw [← OrdinalTriangleAdditivity.cycleSum_tournament_ordinal (blockSize B) (block B)]
  change OrdinalTriangleAdditivity.cycleSum
    (matrix (blockSize B) (fun a => (block B a).entry) (count B)) = _
  rw [cycleSum_eq, OrdinalTriangleAdditivity.cycleSum_tournament]

end TournamentOrdinalReconstruction
#print axioms TournamentOrdinalReconstruction.entry
#print axioms TournamentOrdinalReconstruction.sum_sizes
#print axioms TournamentOrdinalReconstruction.sixth_eq

#print axioms TournamentOrdinalReconstruction.block_strong

#print axioms TournamentOrdinalReconstruction.cycleCount_sum
