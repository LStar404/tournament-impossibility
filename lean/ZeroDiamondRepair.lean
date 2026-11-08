import DiamondFreeRepresentation
import ColorCutNormalization
import ColorTargetModels
import FiniteGraphEditTransport
namespace ZeroDiamondRepair
open DiamondGap ColorTransport

/-- Squared row-sum energy of the original finite tournament, before choosing labels. -/
def tournamentEnergy {V : Type*} [Fintype V] (T : Tournament V) : ℝ :=
  ∑ a : V, (∑ b : V, (T.S a b : ℝ))^2

def finiteEnergy (N : ℕ) (B : Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, (∑ j, B i j)^2

theorem restriction_energy (N : ℕ) (B : ℕ → ℕ → ℝ) :
    finiteEnergy N (fun i j => B i j) = graphEnergy N B := by
  unfold finiteEnergy graphEnergy
  simp_rw [Fin.sum_univ_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun i => (∑ j ∈ Finset.range N, B i j)^2) N

theorem enumeration_energy {V : Type*} [Fintype V] (T : Tournament V)
    {N : ℕ} (e : Fin N ≃ V) :
    finiteEnergy N (fun i j => (T.S (e i) (e j) : ℝ)) = tournamentEnergy T := by
  unfold finiteEnergy tournamentEnergy
  apply Fintype.sum_equiv e
  intro i
  congr 1
  exact e.sum_comp (fun b => (T.S (e i) b : ℝ))

/-- The verified representation with a requested finite cardinality label type. -/
theorem zero_word {V : Type*} [Fintype V] [DecidableEq V] (T : Tournament V)
    (hD : T.diamonds.card = 0) (N : ℕ) (hN : Fintype.card V = N) :
    ∃ (w : List Bool) (e : Fin N ≃ V), w.length = N ∧
      ∀ i j, (T.S (e i) (e j) : ℝ) = colorGraph w i j := by
  obtain ⟨w, e, hl, hm⟩ := DiamondFreeRepresentation.zero_diamonds_color_representation T hD
  refine ⟨w, (Fin.castOrderIso hN.symm).toEquiv.trans e, hl.trans hN, ?_⟩
  intro i j
  exact hm (Fin.cast hN.symm i) (Fin.cast hN.symm j)

/-- The represented word has precisely the energy of the original tournament. -/
theorem represented_energy {V : Type*} [Fintype V] (T : Tournament V)
    {N : ℕ} (w : List Bool) (e : Fin N ≃ V) (_hl : w.length = N)
    (hm : ∀ i j, (T.S (e i) (e j) : ℝ) = colorGraph w i j) :
    graphEnergy N (colorGraph w) = tournamentEnergy T := by
  rw [← restriction_energy]
  have he : finiteEnergy N (fun i j => colorGraph w i j) =
      finiteEnergy N (fun i j => (T.S (e i) (e j) : ℝ)) := by
    unfold finiteEnergy
    simp_rw [hm]
  rw [he]
  exact enumeration_energy T e

/-- The independent two-layer doubling matrix, in ordinary interleaved Fin labels. -/
def flatDoubling (k : ℕ) (B : ℕ → ℕ → ℝ) (i j : Fin (2*k)) : ℝ :=
  let p := (pairLabelEquiv k).symm i
  let q := (pairLabelEquiv k).symm j
  doublingMatrix B p.1 p.2 q.1 q.2

theorem flatDoubling_eq_paired (w : List Bool) (k : ℕ) (hl : w.length = k)
    (i j : Fin (2*k)) : flatDoubling k (colorGraph w) i j = colorGraph (paired w) i j := by
  let p := (pairLabelEquiv k).symm i
  let q := (pairLabelEquiv k).symm j
  have hp : pairIndex p.1 p.2 = i.val := congrArg Fin.val ((pairLabelEquiv k).apply_symm_apply i)
  have hq : pairIndex q.1 q.2 = j.val := congrArg Fin.val ((pairLabelEquiv k).apply_symm_apply j)
  have h := paired_is_doubling w p.1 q.1 p.2 q.2 (by rw [hl]; exact p.1.isLt)
    (by rw [hl]; exact q.1.isLt)
  rw [hp, hq] at h
  exact h.symm

/-- Complete zero-diamond odd repair endpoint: the ORIGINAL tournament,
under one ordinary vertex enumeration, differs from the standard carousel
on at most E(T)/8 distinct undirected edges. -/
theorem zero_diamond_odd_repair {V : Type*} [Fintype V] [DecidableEq V]
    (T : Tournament V) (hD : T.diamonds.card = 0) (k : ℕ)
    (hN : Fintype.card V = 2*k+1) :
    ∃ e : Fin (2*k+1) ≃ V,
      ((finiteMismatch (2*k+1) (fun i j => (T.S (e i) (e j) : ℝ))
        (fun i j => carouselMatrix k i j)).card : ℝ) ≤ tournamentEnergy T / 8 := by
  obtain ⟨w, e₀, hl, hm⟩ := zero_word T hD (2*k+1) hN
  obtain ⟨f, hf, hb⟩ := arbitrary_odd_word_repair w k hl
  rw [hl] at hf hb
  rw [represented_energy T w e₀ hl hm] at hb
  let B : Fin (2*k+1) → Fin (2*k+1) → ℝ := fun i j => colorGraph w i j
  let C : Fin (2*k+1) → Fin (2*k+1) → ℝ :=
    fun i j => colorGraph (alternatingOdd k) (f i) (f j)
  have hbridge := finiteMismatch_nat_restriction (2*k+1) (colorGraph w)
    (colorGraph (alternatingOdd k)) f
  rw [← hbridge] at hb
  let F := restrictNatEquiv (2*k+1) f hf
  let g := (carouselLabelEquiv k).trans F.symm
  have hcount := finiteMismatch_reindex_card B C
    (fun i j => (colorGraph_tournament w).2.1 i j)
    (fun i j => (colorGraph_tournament (alternatingOdd k)).2.1 (f i) (f j)) g
  have hA : (fun i j => B (g i) (g j)) =
      (fun i j => (T.S ((g.trans e₀) i) ((g.trans e₀) j) : ℝ)) := by
    funext i j
    exact (hm (g i) (g j)).symm
  have hC : (fun i j => C (g i) (g j)) = (fun (i j : Fin (2*k+1)) => carouselMatrix k i j) := by
    funext i j
    change colorGraph (alternatingOdd k)
      (f (f.symm ((carouselLabelEquiv k i) : ℕ)))
      (f (f.symm ((carouselLabelEquiv k j) : ℕ))) = carouselMatrix k i j
    rw [f.apply_symm_apply, f.apply_symm_apply]
    exact alternating_carousel_isomorphism k i j
  rw [hA, hC] at hcount
  refine ⟨g.trans e₀, ?_⟩
  rw [hcount]
  exact hb

/-- Complete zero-diamond even repair endpoint: the ORIGINAL tournament,
under one ordinary vertex enumeration, differs from an independently defined
two-layer doubling on at most (E(T)-|V|)/16 distinct undirected edges. -/
theorem zero_diamond_even_repair {V : Type*} [Fintype V] [DecidableEq V]
    (T : Tournament V) (hD : T.diamonds.card = 0) (k : ℕ)
    (hN : Fintype.card V = 2*k) :
    ∃ (baseWord : List Bool) (e : Fin (2*k) ≃ V), baseWord.length = k ∧
      ((finiteMismatch (2*k) (fun i j => (T.S (e i) (e j) : ℝ))
        (flatDoubling k (colorGraph baseWord))).card : ℝ) ≤
        (tournamentEnergy T - Fintype.card V) / 16 := by
  obtain ⟨w, e₀, hl, hm⟩ := zero_word T hD (2*k) hN
  obtain ⟨orient, f, horient, hf, hb⟩ := arbitrary_even_word_repair w k hl
  rw [hl] at hf hb
  rw [represented_energy T w e₀ hl hm] at hb
  let B : Fin (2*k) → Fin (2*k) → ℝ := fun i j => colorGraph w i j
  let C : Fin (2*k) → Fin (2*k) → ℝ :=
    fun i j => colorGraph (paired orient) (f i) (f j)
  have hbridge := finiteMismatch_nat_restriction (2*k) (colorGraph w)
    (colorGraph (paired orient)) f
  rw [← hbridge] at hb
  let g := (restrictNatEquiv (2*k) f hf).symm
  have hcount := finiteMismatch_reindex_card B C
    (fun i j => (colorGraph_tournament w).2.1 i j)
    (fun i j => (colorGraph_tournament (paired orient)).2.1 (f i) (f j)) g
  have hA : (fun i j => B (g i) (g j)) =
      (fun i j => (T.S ((g.trans e₀) i) ((g.trans e₀) j) : ℝ)) := by
    funext i j
    exact (hm (g i) (g j)).symm
  have hC : (fun i j => C (g i) (g j)) = flatDoubling k (colorGraph orient) := by
    funext i j
    change colorGraph (paired orient) (f (f.symm i)) (f (f.symm j)) = _
    rw [f.apply_symm_apply, f.apply_symm_apply]
    exact (flatDoubling_eq_paired orient k horient i j).symm
  rw [hA, hC] at hcount
  refine ⟨orient, g.trans e₀, horient, ?_⟩
  rw [hcount, hN]
  exact hb

#print axioms zero_diamond_odd_repair
#print axioms zero_diamond_even_repair
#print axioms zero_word
#print axioms represented_energy
#print axioms flatDoubling_eq_paired
end ZeroDiamondRepair
