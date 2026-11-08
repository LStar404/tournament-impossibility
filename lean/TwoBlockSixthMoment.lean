import TwoBlockCubeGeneric
import TwoBlockEnergy
import RectangularFrobenius
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace TwoBlockSixthMoment
open Finset Matrix RectangularFrobenius
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def third (A : Matrix ι ι ℝ) : ℝ := sqnorm (A^3)
def u (A : Matrix ι ι ℝ) : ι → ℝ := A.mulVec (TwoBlockEnergy.ones ι)
def v (A : Matrix ι ι ℝ) : ι → ℝ := A.mulVec (u A)

lemma inner_outer_action (M : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    RectangularFrobenius.inner M (outer x y) = dotProduct x (M.mulVec y) := by
  simp only [RectangularFrobenius.inner, outer, Matrix.mulVec, dotProduct]
  apply sum_congr rfl; intro i hi
  rw [mul_sum]
  apply sum_congr rfl; intro j hj
  ring

lemma cube_skew (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = -A j i) :
    ∀ i j, (A^3) i j = -(A^3) j i := by
  have ht : A.transpose = -A := by ext i j; exact hA j i
  have hc : (A^3).transpose = -(A^3) := by
    rw [Matrix.transpose_pow, ht]
    noncomm_ring
  intro i j
  have hh := congrArg (fun M : Matrix ι ι ℝ => M j i) hc
  exact hh

lemma cube_action (A : Matrix ι ι ℝ) :
    (A^3).mulVec (TwoBlockEnergy.ones ι) = A.mulVec (v A) := by
  simp only [v, u]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp [pow_succ, Matrix.mul_assoc]

lemma cube_mixed_left (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = -A j i) :
    RectangularFrobenius.inner (A^3) (outer (u A) (TwoBlockEnergy.ones ι)) = -TwoBlockEnergy.second A := by
  rw [inner_outer_action, cube_action]
  have hh := TwoBlockEnergy.skew_pair A hA (u A) (v A)
  simpa [v, u, TwoBlockEnergy.second, dotProduct, pow_two] using hh

lemma cube_mixed_right (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = -A j i) :
    RectangularFrobenius.inner (A^3) (outer (TwoBlockEnergy.ones ι) (u A)) = TwoBlockEnergy.second A := by
  rw [inner_outer_action, TwoBlockEnergy.skew_pair (A^3) (cube_skew A hA)]
  have hh := cube_mixed_left A hA
  rw [inner_outer_action] at hh
  linarith

lemma mul_ones (A : Matrix ι ι ℝ) :
    A * TwoBlockCubeGeneric.ones ι κ = outer (u A) (TwoBlockEnergy.ones κ) := by
  ext i j
  simp [TwoBlockCubeGeneric.ones, outer, u, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, TwoBlockEnergy.ones]

lemma outer_mul_skew (B : Matrix κ κ ℝ) (hB : ∀ i j, B i j = -B j i)
    (x : ι → ℝ) (y : κ → ℝ) :
    (outer x y * B) = -outer x (B.mulVec y) := by
  ext i j
  simp only [Matrix.mul_apply, outer, Matrix.neg_apply, Matrix.mulVec, dotProduct]
  rw [mul_sum, ← sum_neg_distrib]
  apply sum_congr rfl; intro l hl
  rw [hB l j]; ring

lemma ones_mul (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = -A j i) :
    TwoBlockCubeGeneric.ones κ ι * A = -outer (TwoBlockEnergy.ones κ) (u A) := by
  have he : TwoBlockCubeGeneric.ones κ ι =
      outer (TwoBlockEnergy.ones κ) (TwoBlockEnergy.ones ι) := by
    ext i j; simp [TwoBlockCubeGeneric.ones, outer, TwoBlockEnergy.ones]
  rw [he, outer_mul_skew A hA]
  rfl

lemma square_mul_ones (A : Matrix ι ι ℝ) :
    A^2 * TwoBlockCubeGeneric.ones ι κ = outer (v A) (TwoBlockEnergy.ones κ) := by
  rw [mul_ones]
  congr 1
  unfold u v
  rw [pow_two, ← Matrix.mulVec_mulVec]
  rfl

lemma ones_mul_square (B : Matrix κ κ ℝ) (hB : ∀ i j, B i j = -B j i) :
    TwoBlockCubeGeneric.ones ι κ * B^2 = outer (TwoBlockEnergy.ones ι) (v B) := by
  rw [pow_two, ← Matrix.mul_assoc, ones_mul B hB, Matrix.neg_mul,
    outer_mul_skew B hB, neg_neg]
  rfl

lemma diagonal_cube_norm (A : Matrix ι ι ℝ) (hA : ∀ i j, A i j = -A j i) (c : ℝ) :
    sqnorm (A^3-c • (A*TwoBlockCubeGeneric.ones ι ι+TwoBlockCubeGeneric.ones ι ι*A)) =
      third A + 4*c*TwoBlockEnergy.second A+
      2*(Fintype.card ι : ℝ)*c^2*TwoBlockEnergy.first A := by
  rw [mul_ones, ones_mul A hA, sub_eq_add_neg]
  apply diagonal_block_sqnorm
  · rfl
  · exact TwoBlockEnergy.sum_action A hA
  · simp [u, TwoBlockEnergy.first, pow_two]
  · exact cube_mixed_left A hA
  · exact cube_mixed_right A hA

lemma cross_cube_norm (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : ∀ i j, A i j = -A j i) (hB : ∀ i j, B i j = -B j i) :
    sqnorm (A^2*TwoBlockCubeGeneric.ones ι κ+
      (A*TwoBlockCubeGeneric.ones ι κ)*B+TwoBlockCubeGeneric.ones ι κ*B^2-
      ((Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)) • TwoBlockCubeGeneric.ones ι κ) =
      (Fintype.card κ : ℝ)*TwoBlockEnergy.second A+
      (Fintype.card ι : ℝ)*TwoBlockEnergy.second B+
      3*TwoBlockEnergy.first A*TwoBlockEnergy.first B+
      (Fintype.card ι : ℝ)^3*(Fintype.card κ : ℝ)^3+
      2*(Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)^2*TwoBlockEnergy.first A+
      2*(Fintype.card ι : ℝ)^2*(Fintype.card κ : ℝ)*TwoBlockEnergy.first B := by
  rw [square_mul_ones, mul_ones, outer_mul_skew B hB, ones_mul_square B hB, sub_eq_add_neg]
  have he : TwoBlockCubeGeneric.ones ι κ =
      outer (TwoBlockEnergy.ones ι) (TwoBlockEnergy.ones κ) := by
    ext i j; simp [TwoBlockCubeGeneric.ones, outer, TwoBlockEnergy.ones]
  rw [he]
  apply cross_block_sqnorm
  · exact TwoBlockEnergy.sum_action A hA
  · exact TwoBlockEnergy.sum_action B hB
  · exact TwoBlockEnergy.sum_second_action A hA
  · exact TwoBlockEnergy.sum_second_action B hB
  · simp [u, TwoBlockEnergy.first, pow_two]
  · simp [v, u, TwoBlockEnergy.second, pow_two]
  · simp [u, TwoBlockEnergy.first, pow_two]
  · simp [v, u, TwoBlockEnergy.second, pow_two]

lemma sqnorm_blocks (X : Matrix ι ι ℝ) (Y : Matrix ι κ ℝ)
    (Z : Matrix κ ι ℝ) (W : Matrix κ κ ℝ) :
    sqnorm (fromBlocks X Y Z W) = sqnorm X+sqnorm Y+sqnorm Z+sqnorm W := by
  simp [sqnorm, RectangularFrobenius.inner, Fintype.sum_sum_type, Matrix.fromBlocks, sum_add_distrib] <;> ring

lemma sqnorm_neg_transpose (Y : Matrix ι κ ℝ) : sqnorm (-Y.transpose) = sqnorm Y := by
  simp only [sqnorm, RectangularFrobenius.inner, Matrix.neg_apply, Matrix.transpose_apply, neg_mul_neg]
  exact Finset.sum_comm

lemma joined_skew (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : ∀ i j, A i j = -A j i) (hB : ∀ i j, B i j = -B j i) :
    ∀ i j, TwoBlockCubeGeneric.joined A B i j = -TwoBlockCubeGeneric.joined A B j i := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact hA i j
  · simp [TwoBlockCubeGeneric.joined, TwoBlockCubeGeneric.ones, Matrix.fromBlocks]
  · simp [TwoBlockCubeGeneric.joined, TwoBlockCubeGeneric.ones, Matrix.fromBlocks]
  · exact hB i j

/-- Exact sixth Frobenius moment recurrence for actual skew block matrices. -/
theorem third_join (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : ∀ i j, A i j = -A j i) (hB : ∀ i j, B i j = -B j i) :
    third (TwoBlockEnergy.join A B) = third A+third B+
      6*(Fintype.card κ : ℝ)*TwoBlockEnergy.second A+
      6*(Fintype.card ι : ℝ)*TwoBlockEnergy.second B+
      6*TwoBlockEnergy.first A*TwoBlockEnergy.first B+
      6*(Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)^2*TwoBlockEnergy.first A+
      6*(Fintype.card ι : ℝ)^2*(Fintype.card κ : ℝ)*TwoBlockEnergy.first B+
      2*(Fintype.card ι : ℝ)^3*(Fintype.card κ : ℝ)^3 := by
  let X := A^3-(Fintype.card κ : ℝ) •
    (A*TwoBlockCubeGeneric.ones ι ι+TwoBlockCubeGeneric.ones ι ι*A)
  let Y := A^2*TwoBlockCubeGeneric.ones ι κ+
    (A*TwoBlockCubeGeneric.ones ι κ)*B+TwoBlockCubeGeneric.ones ι κ*B^2-
    ((Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)) • TwoBlockCubeGeneric.ones ι κ
  let Z := -(TwoBlockCubeGeneric.ones κ ι*A^2)-(B*TwoBlockCubeGeneric.ones κ ι)*A-
    B^2*TwoBlockCubeGeneric.ones κ ι+
    ((Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)) • TwoBlockCubeGeneric.ones κ ι
  let W := B^3-(Fintype.card ι : ℝ) •
    (B*TwoBlockCubeGeneric.ones κ κ+TwoBlockCubeGeneric.ones κ κ*B)
  have hc : TwoBlockCubeGeneric.joined A B ^3 = fromBlocks X Y Z W :=
    TwoBlockCubeGeneric.joined_cube A B hA hB
  have hz : Z = -Y.transpose := by
    ext i j
    have hh := cube_skew (TwoBlockCubeGeneric.joined A B) (joined_skew A B hA hB)
      (Sum.inr i) (Sum.inl j)
    rw [hc] at hh
    exact hh
  have hX := diagonal_cube_norm A hA (Fintype.card κ : ℝ)
  have hW := diagonal_cube_norm B hB (Fintype.card ι : ℝ)
  have hY := cross_cube_norm A B hA hB
  change sqnorm (TwoBlockCubeGeneric.joined A B ^3) = _
  rw [hc, sqnorm_blocks, hz, sqnorm_neg_transpose]
  change sqnorm X+sqnorm Y+sqnorm Y+sqnorm W = _
  change sqnorm X = _ at hX
  change sqnorm W = _ at hW
  change sqnorm Y = _ at hY
  simp only [hX, hW, hY]
  ring

end TwoBlockSixthMoment
#print axioms TwoBlockSixthMoment.diagonal_cube_norm
#print axioms TwoBlockSixthMoment.cross_cube_norm

#print axioms TwoBlockSixthMoment.third_join
