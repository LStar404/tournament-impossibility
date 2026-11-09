import PermanentFrozenCoefficientExpansion
import PermanentRestrictionFiber
import PermanentSubsetMinorBridge

/-! Exact coefficients of the literal permanent in terms of the OLD frozen Fk.
This is finite algebra and does not assume an analytic core approximation. -/
noncomputable section
open scoped BigOperators
namespace PermanentFrozenCoefficientBridge
open PermanentSubsetMinorBridge FrozenPartialPairingPolynomial
open PermanentPolynomialCircleTail

variable {n : ℕ} {S : Type*} [CommSemiring S]

lemma powersetCard_univ (k : ℕ) :
    (Finset.univ : Finset (Fin n)).powersetCard k =
      Finset.univ.filter (fun I : Finset (Fin n) => I.card = k) := by
  classical
  ext I
  simp [Finset.mem_powersetCard]

lemma selected_unequal (M : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n))
    (h : I.card ≠ J.card) : selectedPermanent M I J = 0 := by
  rw [selected_eq_subsetWeight]
  exact SubsetPairingScaling.unequal M J I (Ne.symm h)

lemma selected_inner_restrict (M : Matrix (Fin n) (Fin n) S)
    (I : Finset (Fin n)) :
    (∑ J : Finset (Fin n), selectedPermanent M I J) =
      ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard I.card,
        selectedPermanent M I J := by
  classical
  rw [powersetCard_univ]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro J hJ hnJ
  apply selected_unequal
  simpa [eq_comm] using hnJ

lemma selected_product_sum (M : Matrix (Fin n) (Fin n) S)
    (I : Finset (Fin n)) :
    (∑ σ : Equiv.Perm (Fin n), ∏ i ∈ I, M (σ i) i) =
      ((n-I.card).factorial : S) *
        ∑ J : Finset (Fin n), selectedPermanent M I J := by
  classical
  have h := PermanentRestrictionFiber.sum_permutations I (fun i j => M j i)
  calc
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i : I, M (σ i) i := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact (Finset.prod_coe_sort I (fun i => M (σ i) i)).symm
    _ = _ := h

/-- The only multiplicity outside the selected minor is the complement factorial. -/
theorem selected_degree_sum (M : Matrix (Fin n) (Fin n) S) (k : ℕ) :
    (∑ σ : Equiv.Perm (Fin n), ∑ I : Finset (Fin n),
      if I.card=k then ∏ i ∈ I, M (σ i) i else 0) =
      ((n-k).factorial : S) * Fk M k := by
  classical
  rw [Finset.sum_comm]
  have hi (I : Finset (Fin n)) :
      (∑ σ : Equiv.Perm (Fin n), if I.card=k then ∏ i ∈ I, M (σ i) i else 0) =
        if I.card=k then ((n-k).factorial : S) *
          ∑ J : Finset (Fin n), selectedPermanent M I J else 0 := by
    by_cases h : I.card=k
    · simp only [h, ite_true]
      rw [selected_product_sum, h]
    · simp [h]
  simp_rw [hi]
  rw [← Finset.sum_filter]
  rw [← powersetCard_univ]
  rw [Fk_eq_minorSum, minorSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [selected_inner_restrict, (Finset.mem_powersetCard.mp hI).2]

/-- Valid for every k, including k>n where Fk vanishes independently. -/
theorem coefficient_Fk (a : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (permanentPolynomial (fun _ _ => a) M).coeff k =
      a^(n-k) * ((n-k).factorial : ℂ) * Fk M k := by
  rw [PermanentFrozenCoefficientExpansion.coefficient_expansion, selected_degree_sum]
  ring

theorem coefficient_zero_above (a : ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) (hk : n < k) :
    (permanentPolynomial (fun _ _ => a) M).coeff k = 0 := by
  rw [coefficient_Fk, Fk_zero_above_dimension M k hk, mul_zero]

end PermanentFrozenCoefficientBridge

#print axioms PermanentFrozenCoefficientBridge.selected_degree_sum
#print axioms PermanentFrozenCoefficientBridge.coefficient_Fk
