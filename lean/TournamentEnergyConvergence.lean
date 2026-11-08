import TournamentEnergySeries
noncomputable section
namespace TournamentEnergyConvergence
open Finset VectorWeakMajorization TournamentPowerComparison IteratedVectorMajorization TournamentEnergySeries

lemma entry_abs_le {n : ℕ} (B : Tournament n) (i j : Fin n) : |B.entry i j| ≤ 1 := by
  by_cases hij : i=j
  · subst j; simp [B.diagonal]
  · rcases B.unit i j hij with h | h <;> rw [h] <;> norm_num

lemma act_abs_le {n : ℕ} (B : Tournament n) (x : Fin n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hx : ∀ j, |x j| ≤ M) (i : Fin n) : |B.act x i| ≤ (n : ℝ)*M := by
  calc
    _ ≤ ∑ j, |B.entry i j*x j| := by
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, M := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      calc
        _ ≤ 1*M := mul_le_mul (entry_abs_le B i j) (hx j) (abs_nonneg _) (by norm_num)
        _ = M := one_mul M
    _ = _ := by simp

lemma trajectory_ones_bound {n : ℕ} (B : Tournament n) (r : ℕ) (i : Fin n) :
    |trajectory (fun _ => B) (fun _ => (1:ℝ)) r i| ≤ (n : ℝ)^r := by
  induction r generalizing i with
  | zero => simp [trajectory]
  | succ r ih =>
    have h := act_abs_le B (trajectory (fun _ => B) (fun _ => (1:ℝ)) r)
      ((n : ℝ)^r) (pow_nonneg (Nat.cast_nonneg n) r) ih i
    simpa [trajectory, pow_succ', mul_comm] using h

lemma energy_bound (n r : ℕ) (B : Tournament n) :
    energy (matrix B) r ≤ (n : ℝ)*((n : ℝ)^r)^2 := by
  unfold energy
  calc
    _ ≤ ∑ _i : Fin n, ((n : ℝ)^r)^2 := by
      apply sum_le_sum
      intro i hi
      have h := trajectory_ones_bound B r i
      rw [trajectory_eq_mulVec] at h
      have hs := mul_self_le_mul_self (abs_nonneg ((matrix B^r).mulVec (fun _ => (1:ℝ)) i)) h
      simpa [← pow_two, sq_abs] using hs
    _ = _ := by simp

lemma source_bound (n r : ℕ) (B : Tournament n) (q : ℝ) (hq : 0 ≤ q) :
    q^r*energy (matrix B) (r+1) ≤ (n : ℝ)^3*(q*(n : ℝ)^2)^r := by
  have h := mul_le_mul_of_nonneg_left (energy_bound n (r+1) B) (pow_nonneg hq r)
  have hp : (((n : ℝ)^r)^2) = (((n : ℝ)^2)^r) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  calc
    _ ≤ q^r*((n : ℝ)*((n : ℝ)^(r+1))^2) := h
    _ = _ := by rw [pow_succ (n : ℝ) r, mul_pow, hp, mul_pow]; ring

/-- A conservative, explicit convergence domain: q*n²<1. -/
theorem source_summable (n : ℕ) (B : Tournament n) (q : ℝ)
    (hq : 0 ≤ q) (hsmall : q*(n : ℝ)^2 < 1) :
    Summable (fun r : ℕ => q^r*energy (matrix B) (r+1)) := by
  have hg : Summable (fun r : ℕ => (n : ℝ)^3*(q*(n : ℝ)^2)^r) :=
    (summable_geometric_of_lt_one (mul_nonneg hq (sq_nonneg _)) hsmall).mul_left _
  apply hg.of_nonneg_of_le
  · intro r
    apply mul_nonneg (pow_nonneg hq r)
    exact sum_nonneg (fun i hi => sq_nonneg _)
  · intro r
    exact source_bound n r B q hq

/-- Unconditional series comparison on the stated explicit small domain.
This does not assert the larger optimal spectral domain or resolvent equality. -/
theorem source_series_le_small (n : ℕ) (B : Tournament n) (q : ℝ)
    (hq : 0 ≤ q) (hsmall : q*(n : ℝ)^2 < 1) :
    (∑' r : ℕ, q^r*energy (matrix B) (r+1)) ≤
      ∑' r : ℕ, q^r*energy (TransitiveOrbit.T n) (r+1) := by
  apply TournamentEnergySeries.source_series_le n B q hq
  · exact source_summable n B q hq hsmall
  · exact source_summable n (TransitiveOrbit.transitiveTournament n) q hq hsmall
end TournamentEnergyConvergence
#print axioms TournamentEnergyConvergence.source_summable
#print axioms TournamentEnergyConvergence.source_series_le_small
