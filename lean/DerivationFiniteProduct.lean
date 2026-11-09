import Mathlib

noncomputable section
open scoped BigOperators
namespace DerivationFiniteProduct
variable {R A I : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq I]

theorem product (D : Derivation R A A) (s : Finset I) (f : I → A) :
    D (∏ i ∈ s, f i) = ∑ j ∈ s, D (f j) * ∏ i ∈ s.erase j, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha]
    simp only [smul_eq_mul, Finset.erase_insert ha]
    rw [Finset.mul_sum]
    have hh : ∑ j ∈ s, f a * (D (f j) * ∏ i ∈ s.erase j, f i) =
        ∑ j ∈ s, D (f j) * ∏ i ∈ (insert a s).erase j, f i := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjne : a ≠ j := fun he => ha (he ▸ hj)
      rw [Finset.erase_insert_of_ne hjne, Finset.prod_insert (by simp [ha])]
      ring
    rw [hh]
    ring

end DerivationFiniteProduct
#print axioms DerivationFiniteProduct.product
