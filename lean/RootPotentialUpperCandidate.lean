import ActualRootEnergy
import MatrixScalingMassPotential
/-! Verified isolated finite lemma. The missing upper potential direction. -/
set_option autoImplicit false
noncomputable section
namespace RootPotentialUpperCandidate
open Finset Matrix ActualRootEnergy MatrixScalingMassPotential FiniteSymmetricQuadratic
variable {m : ℕ}
lemma weighted_linear_identity (Y : Matrix (Fin m) (Fin m) ℝ) (x y : Fin m → ℝ) :
    (∑ i, ∑ j, Y i j*(x i+y j)) =
      theta x y+∑ k, ActualRootEnergy.residual Y k*vector x y k := by
  have he : (∑ i, ∑ j, Y i j*(x i+y j)) =
      (∑ i, x i*(∑ j,Y i j))+(∑ j,y j*(∑ i,Y i j)) := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => Y i j*y j)]
    simp only [← Finset.sum_mul, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
    · rw [← Finset.mul_sum]; ring
    · rw [← Finset.mul_sum]; ring
  rw [he]
  simp only [ActualRootEnergy.residual, vector, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    ActualHessianFinite.r, ActualHessianFinite.c, ActualHessianFinite.row,
    ActualHessianFinite.col, theta, sub_mul, one_mul, Finset.sum_sub_distrib]
  have hx : (∑ i,x i*(∑ j,Y i j))=∑ i,(∑ j,Y i j)*x i := by
    apply Finset.sum_congr rfl; intro i hi; ring
  have hy : (∑ j,y j*(∑ i,Y i j))=∑ j,(∑ i,Y i j)*y j := by
    apply Finset.sum_congr rfl; intro j hj; ring
  rw [hx,hy]
  ring

lemma theta_upper_residual (Y : Matrix (Fin m) (Fin m) ℝ) (x y : Fin m → ℝ)
    (hY : ∀ i j, 0≤Y i j) (hmass : (∑ i,∑ j,Y i j)=(m:ℝ))
    (hr : root Y x y) : theta x y ≤ -(∑ k,ActualRootEnergy.residual Y k*vector x y k) := by
  have hh : (∑ i,∑ j,Y i j*(1+(x i+y j))) ≤ (m:ℝ) := by
    calc
      _ ≤ ∑ i,∑ j,Y i j*Real.exp (x i+y j) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (x i+y j)]) (hY i j)
      _ = _ := by simp only [hr.1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hex : (∑ i,∑ j,Y i j*(1+(x i+y j))) =
      (∑ i,∑ j,Y i j)+(∑ i,∑ j,Y i j*(x i+y j)) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib]
  rw [hex, hmass, weighted_linear_identity] at hh
  linarith

lemma theta_upper_energy (Y : Matrix (Fin m) (Fin m) ℝ) (x y : Fin m → ℝ)
    (hY : ∀ i j, 0≤Y i j) (hmass : (∑ i,∑ j,Y i j)=(m:ℝ))
    (hr : root Y x y) (D : ℝ)
    (hcontrol : l2 (vector x y)≤D*l2 (ActualRootEnergy.residual Y)) :
    theta x y ≤ D*energy (ActualRootEnergy.residual Y) := by
  have hlin := theta_upper_residual Y x y hY hmass hr
  have hs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m ⊕ Fin m))
    (fun k => -ActualRootEnergy.residual Y k) (vector x y)
  have hcs : -(∑ k,ActualRootEnergy.residual Y k*vector x y k)≤l2 (ActualRootEnergy.residual Y)*l2 (vector x y) := by
    simpa [l2, energy, neg_mul, Finset.sum_neg_distrib] using hs
  have hc := mul_le_mul_of_nonneg_left hcontrol (Real.sqrt_nonneg (energy (ActualRootEnergy.residual Y)))
  have he : l2 (ActualRootEnergy.residual Y)^2=energy (ActualRootEnergy.residual Y) := Real.sq_sqrt (energy_nonneg _)
  change l2 (ActualRootEnergy.residual Y)*l2 (vector x y) ≤
    l2 (ActualRootEnergy.residual Y)*(D*l2 (ActualRootEnergy.residual Y)) at hc
  calc
    _ ≤ _ := hlin.trans (hcs.trans hc)
    _ = D*energy (ActualRootEnergy.residual Y) := by rw [← he]; ring
end RootPotentialUpperCandidate
