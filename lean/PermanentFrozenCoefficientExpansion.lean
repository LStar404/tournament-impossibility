import PermanentPolynomialCircleTail
import FrozenPartialPairingPolynomial
import FiniteFactorialRecovery

/-! Exact first bridge: coefficient expansion of the literal
permanent polynomial. The subsequent restriction-fiber multiplicity (n-k)!
is deliberately not assumed or asserted here. -/
noncomputable section
namespace PermanentFrozenCoefficientExpansion
open PermanentPolynomialCircleTail

lemma selected_product {n : ℕ} (s : Finset (Fin n)) (a : Fin n → ℂ) :
    (∏ i ∈ s, Polynomial.X * Polynomial.C (a i)) =
      Polynomial.monomial s.card (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, ih, Finset.card_insert_of_notMem hi, Finset.prod_insert hi]
    rw [show Polynomial.X * Polynomial.C (a i) = Polynomial.monomial 1 (a i) by
      simp [Polynomial.X, Polynomial.monomial_mul_C]]
    rw [Polynomial.monomial_mul_monomial]
    simp [Nat.add_comm]

/-- All selected positions are retained before any restriction regrouping. -/
theorem polynomial_expansion {n : ℕ} (a : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    permanentPolynomial (fun _ _ => a) M =
      ∑ σ : Equiv.Perm (Fin n), ∑ I : Finset (Fin n),
        Polynomial.monomial I.card (a ^ Iᶜ.card * ∏ i ∈ I, M (σ i) i) := by
  classical
  unfold permanentPolynomial Matrix.permanent
  apply Finset.sum_congr rfl
  intro σ hσ
  simp_rw [add_comm (Polynomial.C a), Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro I hI
  rw [selected_product]
  have hc : (∏ i ∈ Iᶜ, Polynomial.C a) = Polynomial.C (a ^ Iᶜ.card) := by
    simp
  rw [hc, Polynomial.monomial_mul_C]
  congr 1
  ring

/-- Exact coefficient formula, still indexed by full permutations. -/
theorem coefficient_expansion {n : ℕ} (a : ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (permanentPolynomial (fun _ _ => a) M).coeff k =
      a ^ (n-k) * ∑ σ : Equiv.Perm (Fin n),
        ∑ I : Finset (Fin n), if I.card = k then ∏ i ∈ I, M (σ i) i else 0 := by
  classical
  rw [polynomial_expansion]
  simp only [Polynomial.finsetSum_coeff]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : I.card = k
  · have hcomp : Iᶜ.card = n-k := by simpa [h] using Finset.card_compl I
    simp [Polynomial.coeff_monomial, h, hcomp]
  · simp [Polynomial.coeff_monomial, h, Ne.symm h]

/-- Baseline J/n specialization. No normalization or completion count has
been silently absorbed into Fk. -/
theorem averaging_coefficient_expansion {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (permanentPolynomial (fun _ _ => (n : ℂ)⁻¹) M).coeff k =
      ((n : ℂ)⁻¹) ^ (n-k) * ∑ σ : Equiv.Perm (Fin n),
        ∑ I : Finset (Fin n), if I.card = k then ∏ i ∈ I, M (σ i) i else 0 :=
  coefficient_expansion _ M k

end PermanentFrozenCoefficientExpansion
#print axioms PermanentFrozenCoefficientExpansion.coefficient_expansion
