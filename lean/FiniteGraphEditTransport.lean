import ColorGraphRepair
namespace ColorTransport

/-- Restrict an ordinary natural-label permutation preserving the finite vertex
set. Its inverse also preserves this set by the same iff hypothesis. -/
def restrictNatEquiv (N : ℕ) (e : Equiv ℕ ℕ)
    (he : ∀ i, e i < N ↔ i < N) : Fin N ≃ Fin N where
  toFun i := ⟨e i, (he i).mpr i.isLt⟩
  invFun j := ⟨e.symm j, (he (e.symm j)).mp (by simp)⟩
  left_inv i := by apply Fin.ext; simp
  right_inv j := by apply Fin.ext; simp

@[simp] theorem restrictNatEquiv_apply (N : ℕ) (e : Equiv ℕ ℕ)
    (he : ∀ i, e i < N ↔ i < N) (i : Fin N) :
    (restrictNatEquiv N e he i).val = e i := rfl

/-- Actual distinct undirected differing edges, counted once by i<j. -/
noncomputable def finiteMismatch (N : ℕ) (B C : Fin N → Fin N → ℝ) :
    Finset (Fin N × Fin N) := by
  classical
  exact Finset.univ.filter (fun p => p.1 < p.2 ∧ B p.1 p.2 ≠ C p.1 p.2)

private noncomputable def lowerMismatch (N : ℕ) (B C : Fin N → Fin N → ℝ) :
    Finset (Fin N × Fin N) := by
  classical
  exact Finset.univ.filter (fun p => p.2 < p.1 ∧ B p.1 p.2 ≠ C p.1 p.2)

private noncomputable def directedMismatch (N : ℕ) (B C : Fin N → Fin N → ℝ) :
    Finset (Fin N × Fin N) := by
  classical
  exact Finset.univ.filter (fun p => B p.1 p.2 ≠ C p.1 p.2)

private theorem mismatch_swap {N : ℕ} (B C : Fin N → Fin N → ℝ)
    (hB : ∀ i j, B i j = -B j i) (hC : ∀ i j, C i j = -C j i) (i j : Fin N) :
    B i j ≠ C i j ↔ B j i ≠ C j i := by
  rw [hB i j, hC i j]
  simp

private theorem upper_lower_card {N : ℕ} (B C : Fin N → Fin N → ℝ)
    (hB : ∀ i j, B i j = -B j i) (hC : ∀ i j, C i j = -C j i) :
    (finiteMismatch N B C).card = (lowerMismatch N B C).card := by
  classical
  apply Finset.card_bij (fun p _ => (p.2,p.1))
  · intro p hp
    obtain ⟨hlt,hne⟩ : p.1 < p.2 ∧ B p.1 p.2 ≠ C p.1 p.2 := by simpa [finiteMismatch] using hp
    simpa [lowerMismatch] using And.intro hlt ((mismatch_swap B C hB hC _ _).mp hne)
  · intro p hp q hq he
    exact Prod.swap_injective he
  · intro p hp
    obtain ⟨hlt,hne⟩ : p.2 < p.1 ∧ B p.1 p.2 ≠ C p.1 p.2 := by simpa [lowerMismatch] using hp
    refine ⟨(p.2,p.1), ?_, rfl⟩
    simpa [finiteMismatch] using And.intro hlt ((mismatch_swap B C hB hC _ _).mp hne)

private theorem directed_card_twice {N : ℕ} (B C : Fin N → Fin N → ℝ)
    (hB : ∀ i j, B i j = -B j i) (hC : ∀ i j, C i j = -C j i) :
    (directedMismatch N B C).card = 2*(finiteMismatch N B C).card := by
  classical
  have hunion : directedMismatch N B C = finiteMismatch N B C ∪ lowerMismatch N B C := by
    ext p
    simp only [directedMismatch, finiteMismatch, lowerMismatch,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hne
      have hij : p.1 ≠ p.2 := by
        intro he
        have hb := hB p.1 p.1
        have hc := hC p.1 p.1
        rw [← he] at hne
        apply hne
        linarith
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact Or.inl ⟨hlt,hne⟩
      · exact Or.inr ⟨hgt,hne⟩
    · rintro (⟨_,hne⟩ | ⟨_,hne⟩) <;> exact hne
  have hdis : Disjoint (finiteMismatch N B C) (lowerMismatch N B C) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' : p.1 < p.2 := (by simpa [finiteMismatch] using hp : p.1<p.2 ∧ _).1
    have hq' : p.2 < p.1 := (by simpa [lowerMismatch] using hq : p.2<p.1 ∧ _).1
    exact (lt_asymm hp' hq')
  rw [hunion, Finset.card_union_of_disjoint hdis, ← upper_lower_card B C hB hC]
  omega

private theorem directed_reindex_card {N : ℕ} (B C : Fin N → Fin N → ℝ)
    (e : Fin N ≃ Fin N) :
    (directedMismatch N (fun i j => B (e i) (e j)) (fun i j => C (e i) (e j))).card =
      (directedMismatch N B C).card := by
  classical
  apply Finset.card_bij (fun p _ => (e p.1,e p.2))
  · intro p hp
    simpa [directedMismatch] using hp
  · intro p hp q hq he
    apply Prod.ext
    · exact e.injective (congrArg Prod.fst he)
    · exact e.injective (congrArg Prod.snd he)
  · intro p hp
    refine ⟨(e.symm p.1,e.symm p.2), ?_, ?_⟩
    · simpa [directedMismatch] using hp
    · simp

/-- Simultaneously applying one ordinary finite vertex permutation to two skew
matrices leaves their actual undirected differing-edge cardinality unchanged. -/
theorem finiteMismatch_reindex_card {N : ℕ} (B C : Fin N → Fin N → ℝ)
    (hB : ∀ i j, B i j = -B j i) (hC : ∀ i j, C i j = -C j i)
    (e : Fin N ≃ Fin N) :
    (finiteMismatch N (fun i j => B (e i) (e j)) (fun i j => C (e i) (e j))).card =
      (finiteMismatch N B C).card := by
  have h := directed_reindex_card B C e
  rw [directed_card_twice _ _ (fun i j => hB (e i) (e j))
      (fun i j => hC (e i) (e j)), directed_card_twice B C hB hC] at h
  omega

/-- Direct bridge to the existing natural-label discrepancy set. The relabeling
is arbitrary here; preserving the finite vertex set can be supplied separately
when it is needed to interpret e as a finite graph isomorphism. -/
theorem finiteMismatch_nat_restriction (N : ℕ) (B C : ℕ → ℕ → ℝ) (e : Equiv ℕ ℕ) :
    (finiteMismatch N (fun i j => B i j) (fun i j => C (e i) (e j))).card =
      (mismatchEdges N B C e).card := by
  classical
  apply Finset.card_bij (fun p _ => (p.1.val,p.2.val))
  · intro p hp
    obtain ⟨hlt,hne⟩ : p.1 < p.2 ∧ B p.1 p.2 ≠ C (e p.1) (e p.2) := by
      simpa [finiteMismatch] using hp
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr p.1.isLt, Finset.mem_range.mpr p.2.isLt⟩, hlt, Ne.symm hne⟩
  · intro p hp q hq he
    apply Prod.ext
    · apply Fin.ext; exact congrArg Prod.fst he
    · apply Fin.ext; exact congrArg Prod.snd he
  · intro p hp
    obtain ⟨⟨hi,hj⟩,hlt,hne⟩ : (p.1<N ∧ p.2<N) ∧ p.1<p.2 ∧ C (e p.1) (e p.2) ≠ B p.1 p.2 := by
      simpa [mismatchEdges] using hp
    refine ⟨(⟨p.1,hi⟩,⟨p.2,hj⟩), ?_, rfl⟩
    simpa [finiteMismatch] using And.intro hlt (Ne.symm hne)

/-- Identity-label specialization of the natural/finite discrepancy bridge. -/
theorem finiteMismatch_nat_identity (N : ℕ) (B C : ℕ → ℕ → ℝ) :
    (finiteMismatch N (fun i j => B i j) (fun i j => C i j)).card =
      (mismatchEdges N B C (Equiv.refl ℕ)).card := by
  exact finiteMismatch_nat_restriction N B C (Equiv.refl ℕ)

#print axioms restrictNatEquiv
#print axioms finiteMismatch_reindex_card
#print axioms finiteMismatch_nat_restriction
#print axioms finiteMismatch_nat_identity
end ColorTransport
