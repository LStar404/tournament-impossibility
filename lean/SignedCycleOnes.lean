import TransitiveOrbit
noncomputable section
namespace SignedCycleOnes
open Finset Matrix TransitiveOrbit

/-- The first k coordinates are negative, the rest positive. -/
def step (d k : ℕ) (i : Fin (d+1)) : ℝ := if i.val < k then -1 else 1

lemma J_action_rotate (d : ℕ) (x : Fin (d+1) → ℝ) (j : Fin (d+1)) :
    (J d).mulVec x (finRotate (d+1) j) = epsilon d j * x j := by
  simp [Matrix.mulVec, dotProduct, TransitiveOrbit.J, ite_mul]

/-- One negative cyclic shift extends the negative prefix by one coordinate. -/
lemma J_step (d k : ℕ) (hk : k < d+1) :
    (J d).mulVec (step d k) = step d (k+1) := by
  funext i
  obtain ⟨j, rfl⟩ := (finRotate (d+1)).surjective i
  rw [J_action_rotate]
  by_cases hj : j = Fin.last d
  · subst j
    simp [epsilon, step, finRotate_last, show ¬ d < k by omega]
  · have hp := coe_finRotate_of_ne_last hj
    simp only [epsilon, if_neg hj, one_mul, step, hp]
    have he : (j.val+1 < k+1) ↔ (j.val < k) := by omega
    simp only [he]

/-- Exact action of every prefix-length power on the all-one vector.
The endpoint k=d+1 is included, in particular dimension one and k=1. -/
theorem J_power_ones (d k : ℕ) (hk : k ≤ d+1) :
    (J d ^ k).mulVec (fun _ => (1:ℝ)) = step d k := by
  induction k with
  | zero =>
    funext i
    simp [step]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega)]
    exact J_step d k (by omega)

lemma J_sum_sq (d : ℕ) (x : Fin (d+1) → ℝ) :
    (∑ i, ((J d).mulVec x i)^2) = ∑ i, (x i)^2 := by
  rw [← Equiv.sum_comp (finRotate (d+1)) (fun i => ((J d).mulVec x i)^2)]
  apply sum_congr rfl
  intro i hi
  rw [J_action_rotate, mul_pow, epsilon_pow, one_mul]

/-- Every integer power of the actual shift preserves the squared norm. -/
theorem J_power_sum_sq (d k : ℕ) (x : Fin (d+1) → ℝ) :
    (∑ i, ((J d ^ k).mulVec x i)^2) = ∑ i, (x i)^2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, J_sum_sq]
    exact ih

lemma powers_commute (d r k : ℕ) :
    T (d+1)^r * J d^k = J d^k * T (d+1)^r := by
  exact (show Commute (T (d+1)) (J d) from T_commutes_J d).pow_pow r k

/-- The transitive orbit norm is unchanged by any signed cyclic input shift. -/
theorem transitive_shift_sum_sq (d r k : ℕ) (x : Fin (d+1) → ℝ) :
    (∑ i, ((T (d+1)^r).mulVec ((J d^k).mulVec x) i)^2) =
      ∑ i, ((T (d+1)^r).mulVec x i)^2 := by
  rw [Matrix.mulVec_mulVec, powers_commute, ← Matrix.mulVec_mulVec]
  exact J_power_sum_sq d k _

/-- The explicit step vector has the same transitive orbit norm as all ones. -/
theorem transitive_step_sum_sq (d r k : ℕ) (hk : k ≤ d+1) :
    (∑ i, ((T (d+1)^r).mulVec (step d k) i)^2) =
      ∑ i, ((T (d+1)^r).mulVec (fun _ => (1:ℝ)) i)^2 := by
  rw [← J_power_ones d k hk]
  exact transitive_shift_sum_sq d r k _
end SignedCycleOnes
#print axioms SignedCycleOnes.J_power_ones
#print axioms SignedCycleOnes.J_power_sum_sq
#print axioms SignedCycleOnes.transitive_step_sum_sq
