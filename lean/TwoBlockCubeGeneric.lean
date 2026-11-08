import Mathlib
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace TwoBlockCubeGeneric
open Finset Matrix
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
  [DecidableEq ι] [DecidableEq κ]

def ones (ι κ : Type*) : Matrix (ι) (κ) ℝ := fun _ _ => 1

def joined (A : Matrix (ι) (ι) ℝ)
    (B : Matrix (κ) (κ) ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  fromBlocks A (ones ι κ) (-(ones κ ι)) B

/-- Exact block cube before invoking skewness or simplifying rank-one terms. -/
theorem cube_raw (A : Matrix (ι) (ι) ℝ)
    (B : Matrix (κ) (κ) ℝ) (J : Matrix (ι) (κ) ℝ)
    (L : Matrix (κ) (ι) ℝ) :
    (fromBlocks A J (-L) B)^3 = fromBlocks
      (A^3-(J*L)*A-(A*J)*L-(J*B)*L)
      (A^2*J-(J*L)*J+(A*J)*B+J*B^2)
      (-(L*A^2)-(B*L)*A-(B^2*L)+(L*J)*L)
      (B^3-(L*A)*J-(B*L)*J-(L*J)*B) := by
  rw [show (3:ℕ)=2+1 by rfl, pow_succ, pow_two,
    fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, pow_succ, pow_two, pow_one, pow_zero, Matrix.mul_one, Matrix.one_mul] <;>
    abel

lemma ones_mul_ones (ι κ τ : Type*) [Fintype ι] [Fintype κ] [Fintype τ] :
    ones ι κ * ones κ τ = (Fintype.card κ : ℝ) • ones ι τ := by
  ext i j
  simp [ones, Matrix.mul_apply]

omit [DecidableEq ι] in
lemma skew_total_zero (A : Matrix (ι) (ι) ℝ)
    (hA : ∀ i j, A i j = -A j i) : (∑ i, ∑ j, A i j) = 0 := by
  have h : (∑ i, ∑ j, A i j) = -(∑ i, ∑ j, A i j) := by
    calc
      _ = ∑ i : ι, ∑ j : ι, A j i := Finset.sum_comm
      _ = _ := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl; intro i hi
        rw [← sum_neg_distrib]
        apply sum_congr rfl; intro j hj
        exact hA j i
  linarith

lemma ones_sandwich_zero (ι κ τ : Type*) [Fintype ι] [Fintype κ] [Fintype τ] (B : Matrix (κ) (κ) ℝ)
    (hB : ∀ i j, B i j = -B j i) :
    ones ι κ * B * ones κ τ = 0 := by
  ext i j
  simp only [Matrix.mul_apply, ones, one_mul, mul_one, Matrix.zero_apply]
  rw [sum_comm]
  exact skew_total_zero B hB

lemma ones_triple (ι κ : Type*) [Fintype ι] [Fintype κ] :
    (ones ι κ * ones κ ι) * ones ι κ = ((Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)) • ones ι κ := by
  rw [ones_mul_ones, Matrix.smul_mul, ones_mul_ones, smul_smul, mul_comm]

/-- All four blocks of the cube of an ordinal two-block skew matrix.
The only analytic input is the exact identity 1ᵀA1=1ᵀB1=0. -/
theorem joined_cube (A : Matrix (ι) (ι) ℝ)
    (B : Matrix (κ) (κ) ℝ)
    (hA : ∀ i j, A i j = -A j i) (hB : ∀ i j, B i j = -B j i) :
    joined A B ^ 3 = fromBlocks
      (A^3 - (Fintype.card κ : ℝ) • (A*ones ι ι + ones ι ι*A))
      (A^2*ones ι κ + (A*ones ι κ)*B + ones ι κ*B^2 -
        ((Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)) • ones ι κ)
      (-(ones κ ι*A^2) - (B*ones κ ι)*A - B^2*ones κ ι +
        ((Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)) • ones κ ι)
      (B^3 - (Fintype.card ι : ℝ) • (B*ones κ κ + ones κ κ*B)) := by
  unfold joined
  rw [cube_raw]
  congr 1
  · rw [ones_sandwich_zero ι κ ι B hB, sub_zero, ones_mul_ones,
      Matrix.smul_mul, Matrix.mul_assoc A, ones_mul_ones, Matrix.mul_smul,
      smul_add]
    abel
  · rw [ones_triple]
    abel
  · rw [ones_triple, mul_comm (Fintype.card κ : ℝ) (Fintype.card ι : ℝ)]
  · rw [ones_sandwich_zero κ ι κ A hA, sub_zero, ones_mul_ones,
      Matrix.smul_mul, Matrix.mul_assoc B, ones_mul_ones, Matrix.mul_smul,
      smul_add]
    abel
end TwoBlockCubeGeneric
#print axioms TwoBlockCubeGeneric.cube_raw
#print axioms TwoBlockCubeGeneric.joined_cube
