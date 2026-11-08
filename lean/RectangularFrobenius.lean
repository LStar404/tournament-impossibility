import Mathlib
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace RectangularFrobenius
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def inner (X Y : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, X i j * Y i j
def sqnorm (X : Matrix ι κ ℝ) : ℝ := inner X X
def outer (u : ι → ℝ) (v : κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => u i * v j

lemma inner_add_left (X Y Z : Matrix ι κ ℝ) :
    inner (X+Y) Z = inner X Z + inner Y Z := by
  simp [inner, add_mul, sum_add_distrib]
lemma inner_add_right (X Y Z : Matrix ι κ ℝ) :
    inner X (Y+Z) = inner X Y + inner X Z := by
  simp [inner, mul_add, sum_add_distrib]
lemma inner_neg_left (X Y : Matrix ι κ ℝ) :
    inner (-X) Y = -inner X Y := by simp [inner]
lemma inner_neg_right (X Y : Matrix ι κ ℝ) :
    inner X (-Y) = -inner X Y := by simp [inner]
lemma inner_smul_left (c : ℝ) (X Y : Matrix ι κ ℝ) :
    inner (c • X) Y = c * inner X Y := by
  unfold inner
  rw [Finset.mul_sum]
  apply sum_congr rfl; intro i hi
  rw [Finset.mul_sum]
  apply sum_congr rfl; intro j hj
  simp [mul_assoc]
lemma inner_smul_right (c : ℝ) (X Y : Matrix ι κ ℝ) :
    inner X (c • Y) = c * inner X Y := by
  have he : inner X (c • Y) = inner (c • Y) X := by
    unfold inner
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj; ring
  rw [he, inner_smul_left]
  congr 1
  unfold inner
  apply sum_congr rfl; intro i hi
  apply sum_congr rfl; intro j hj; ring

lemma inner_outer (u v : ι → ℝ) (p q : κ → ℝ) :
    inner (outer u p) (outer v q) = (∑ i, u i*v i) * (∑ j, p j*q j) := by
  unfold inner outer
  have he : (∑ i, ∑ j, u i*p j*(v i*q j)) =
      ∑ i, (u i*v i)*(∑ j, p j*q j) := by
    apply sum_congr rfl; intro i hi
    rw [mul_sum]
    apply sum_congr rfl; intro j hj; ring
  rw [he, sum_mul]

lemma inner_comm (X Y : Matrix ι κ ℝ) : inner X Y = inner Y X := by
  unfold inner
  apply sum_congr rfl; intro i hi
  apply sum_congr rfl; intro j hj; ring

/-- The diagonal cube-block norm once its two mixed products are identified. -/
theorem diagonal_block_sqnorm (M : Matrix ι ι ℝ)
    (u : ι → ℝ) (c g e f : ℝ)
    (hg : inner M M = g) (hu : (∑ i, u i)=0) (he : (∑ i, u i*u i)=e)
    (hleft : inner M (outer u (fun _ : ι => 1)) = -f)
    (hright : inner M (outer (fun _ : ι => 1) u) = f) :
    sqnorm (M + -(c • (outer u (fun _ : ι => 1) +
      -outer (fun _ : ι => 1) u))) = g+4*c*f+2*(Fintype.card ι : ℝ)*c^2*e := by
  have hl' : inner (outer u (fun _ : ι => 1)) M = -f := by rw [inner_comm]; exact hleft
  have hr' : inner (outer (fun _ : ι => 1) u) M = f := by rw [inner_comm]; exact hright
  simp only [sqnorm, inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    inner_smul_left, inner_smul_right]
  rw [hg, hleft, hright, hl', hr']
  simp only [inner_outer, one_mul, mul_one, sum_const, card_univ, nsmul_eq_mul]
  rw [hu, he]
  ring

/-- Squared norm of the off-diagonal cube block, using only finite vector data. -/
theorem cross_block_sqnorm     (u v : ι → ℝ) (p q : κ → ℝ) (eA fA eB fB : ℝ)
    (hu : (∑ i, u i)=0) (hp : (∑ j, p j)=0)
    (hv : (∑ i, v i) = -eA) (hq : (∑ j, q j) = -eB)
    (huu : (∑ i, u i*u i)=eA) (hvv : (∑ i, v i*v i)=fA)
    (hpp : (∑ j, p j*p j)=eB) (hqq : (∑ j, q j*q j)=fB) :
    sqnorm (outer v (fun _ : κ => 1) + -outer u p +
      outer (fun _ : ι => 1) q +
      -(((Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)) • outer (fun _ : ι => 1) (fun _ : κ => 1))) =
      (Fintype.card κ : ℝ)*fA + (Fintype.card ι : ℝ)*fB + 3*eA*eB + (Fintype.card ι : ℝ)^3*(Fintype.card κ : ℝ)^3 +
      2*(Fintype.card ι : ℝ)*(Fintype.card κ : ℝ)^2*eA + 2*(Fintype.card ι : ℝ)^2*(Fintype.card κ : ℝ)*eB := by
  simp only [sqnorm, inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    inner_smul_left, inner_smul_right, inner_outer]
  simp only [one_mul, mul_one, sum_const, card_univ, nsmul_eq_mul]
  rw [hu, hp, hv, hq, huu, hvv, hpp, hqq]
  ring
end RectangularFrobenius
#print axioms RectangularFrobenius.cross_block_sqnorm
