import DerivationFiniteProduct

noncomputable section
open scoped BigOperators
namespace DerivationDeterminantColumns
open Matrix
variable {R A I : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype I] [DecidableEq I]

theorem replaced_product (M : Matrix I I A) (D : Derivation R A A) (σ : Equiv.Perm I) (j : I) :
    (∏ i, (M.updateCol j (fun r => D (M r j))) (σ i) i) =
      D (M (σ j) j) * ∏ i ∈ Finset.univ.erase j, M (σ i) i := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Matrix.updateCol_apply, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp [Matrix.updateCol_apply, (Finset.mem_erase.mp hi).1]

theorem determinant_columns (D : Derivation R A A) (M : Matrix I I A) :
    D M.det = ∑ j, (M.updateCol j (fun i => D (M i j))).det := by
  rw [Matrix.det_apply, map_sum]
  simp only [Derivation.map_smul_of_tower, DerivationFiniteProduct.product, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [replaced_product]

end DerivationDeterminantColumns
#print axioms DerivationDeterminantColumns.determinant_columns
