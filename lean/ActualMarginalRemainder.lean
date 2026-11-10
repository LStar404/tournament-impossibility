import ExpRemainderLipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Matrix.Normed

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Literal exponential row/column marginals and their
finite linear and nonlinear parts. All norms here are ordinary Pi sup norms. -/
set_option autoImplicit false
noncomputable section
namespace ActualMarginalRemainder
open Finset ExpRemainderLipschitz
variable {m : ℕ}
abbrev V (m : ℕ) := (Fin m ⊕ Fin m) → ℝ

def edge (z : V m) (i j : Fin m) := z (Sum.inl i) + z (Sum.inr j)
def marginals (M : Matrix (Fin m) (Fin m) ℝ) (z : V m) : V m :=
  Sum.elim (fun i => (∑ j, M i j * Real.exp (edge z i j))-1)
    (fun j => (∑ i, M i j * Real.exp (edge z i j))-1)
def linearPart (M : Matrix (Fin m) (Fin m) ℝ) (z : V m) : V m :=
  Sum.elim (fun i => ∑ j, M i j * edge z i j)
    (fun j => ∑ i, M i j * edge z i j)
def residual (M : Matrix (Fin m) (Fin m) ℝ) (z : V m) : V m :=
  Sum.elim (fun i => ∑ j, M i j * remainder (edge z i j))
    (fun j => ∑ i, M i j * remainder (edge z i j))
def signedMass (z : V m) := (∑ i, z (Sum.inl i)) - ∑ j, z (Sum.inr j)

def hessian (M : Matrix (Fin m) (Fin m) ℝ) : V m →L[ℝ] V m :=
  ContinuousLinearMap.mk
    { toFun := linearPart M
      map_add' := by
        intro z w
        funext k
        cases k <;> simp [linearPart, edge, mul_add, sum_add_distrib] <;> ring
      map_smul' := by
        intro c z
        funext k
        cases k <;> simp [linearPart, edge, mul_add, mul_sum, mul_assoc, mul_left_comm] }
    (by apply LinearMap.continuous_of_finiteDimensional)

@[simp] lemma hessian_apply (M : Matrix (Fin m) (Fin m) ℝ) (z : V m) :
    hessian M z = linearPart M z := rfl

@[simp] lemma residual_zero (M : Matrix (Fin m) (Fin m) ℝ) : residual M 0 = 0 := by
  funext k
  cases k <;> simp [residual, edge]

lemma marginal_decomposition (M : Matrix (Fin m) (Fin m) ℝ) (z : V m) :
    marginals M z = marginals M 0 + hessian M z + residual M z := by
  funext k
  cases k <;>
    simp [marginals, hessian_apply, linearPart, residual, remainder, edge,
      mul_sub, sum_sub_distrib] <;> ring

lemma signedMass_marginals (M : Matrix (Fin m) (Fin m) ℝ) (z : V m) :
    signedMass (marginals M z) = 0 := by
  simp only [signedMass, marginals, Sum.elim_inl, Sum.elim_inr, sum_sub_distrib]
  rw [sum_comm]
  simp

lemma signedMass_residual (M : Matrix (Fin m) (Fin m) ℝ) (z : V m) :
    signedMass (residual M z) = 0 := by
  simp only [signedMass, residual, Sum.elim_inl, Sum.elim_inr]
  rw [sum_comm]
  simp

lemma edge_norm_bound (z : V m) {a : ℝ} (hz : ‖z‖ ≤ a) (i j : Fin m) :
    ‖edge z i j‖ ≤ 2*a := by
  have hl := norm_le_pi_norm z (Sum.inl i)
  have hr := norm_le_pi_norm z (Sum.inr j)
  exact (norm_add_le (z (Sum.inl i)) (z (Sum.inr j))).trans (by linarith)

lemma edge_sub_norm_bound (z w : V m) (i j : Fin m) :
    ‖edge z i j - edge w i j‖ ≤ 2*‖z-w‖ := by
  have he : edge z i j - edge w i j =
      (z-w) (Sum.inl i) + (z-w) (Sum.inr j) := by simp [edge]; ring
  rw [he]
  have hl := norm_le_pi_norm (z-w) (Sum.inl i)
  have hr := norm_le_pi_norm (z-w) (Sum.inr j)
  exact (norm_add_le ((z-w) (Sum.inl i)) ((z-w) (Sum.inr j))).trans (by linarith)

lemma weighted_sum_bound {ι : Type*} [Fintype ι] (p v : ι → ℝ) {S B : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hS : (∑ i, p i) ≤ S) (hB : 0 ≤ B)
    (hv : ∀ i, ‖v i‖ ≤ B) : ‖∑ i, p i*v i‖ ≤ S*B := by
  calc
    _ ≤ ∑ i, ‖p i*v i‖ := norm_sum_le _ _
    _ = ∑ i, p i*‖v i‖ := by simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg, hp]
    _ ≤ ∑ i, p i*B := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (hp i))
    _ = (∑ i, p i)*B := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hS hB

/-- The dimension-free nonlinear remainder bound is derived from actual entries. -/
theorem residual_sub_bound (M : Matrix (Fin m) (Fin m) ℝ) {S a : ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hS : 0 ≤ S) (ha : 0 ≤ a)
    (hr : ∀ i, (∑ j, M i j) ≤ S) (hc : ∀ j, (∑ i, M i j) ≤ S)
    (z w : V m) (hz : ‖z‖ ≤ a) (hw : ‖w‖ ≤ a) :
    ‖residual M z - residual M w‖ ≤
      (2*S*(Real.exp (2*a)-1))*‖z-w‖ := by
  have he : 0 ≤ Real.exp (2*a)-1 := by
    have := Real.add_one_le_exp (2*a); linarith
  have hb (i j : Fin m) :
      ‖remainder (edge z i j)-remainder (edge w i j)‖ ≤
        (Real.exp (2*a)-1)*(2*‖z-w‖) :=
    (remainder_sub_bound (by positivity) (edge_norm_bound z hz i j)
      (edge_norm_bound w hw i j)).trans
      (mul_le_mul_of_nonneg_left (edge_sub_norm_bound z w i j) he)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  cases k with
  | inl i =>
    have h := weighted_sum_bound (fun j => M i j)
      (fun j => remainder (edge z i j)-remainder (edge w i j))
      (hM i) (hr i) (by positivity) (hb i)
    simpa [residual, ← sum_sub_distrib, ← mul_sub, mul_assoc, mul_left_comm, mul_comm] using h
  | inr j =>
    have h := weighted_sum_bound (fun i => M i j)
      (fun i => remainder (edge z i j)-remainder (edge w i j))
      (fun i => hM i j) (hc j) (by positivity) (fun i => hb i j)
    simpa [residual, ← sum_sub_distrib, ← mul_sub, mul_assoc, mul_left_comm, mul_comm] using h

end ActualMarginalRemainder
#print axioms ActualMarginalRemainder.marginal_decomposition
#print axioms ActualMarginalRemainder.residual_sub_bound
