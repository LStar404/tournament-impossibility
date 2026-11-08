import TournamentEnergyConvergence
noncomputable section
namespace TournamentEnergyRowDomain
open Finset VectorWeakMajorization TournamentPowerComparison IteratedVectorMajorization TournamentEnergySeries
open TournamentEnergyConvergence

def rowBase (n : ℕ) : ℝ := ((n-1 : ℕ) : ℝ)

lemma act_abs_le {n : ℕ} (B : Tournament n) (x : Fin n → ℝ) (M : ℝ)
    (hx : ∀ j, |x j| ≤ M) (i : Fin n) : |B.act x i| ≤ rowBase n * M := by
  have he : (∑ j ∈ (univ : Finset (Fin n)).erase i, B.entry i j*x j) = B.act x i := by
    simpa [Tournament.act] using
      (sum_erase (univ : Finset (Fin n)) (f := fun j => B.entry i j*x j) (a := i)
        (by simp [B.diagonal]))
  rw [← he]
  calc
    _ ≤ ∑ j ∈ (univ : Finset (Fin n)).erase i, |B.entry i j*x j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ (univ : Finset (Fin n)).erase i, M := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      calc
        _ ≤ 1*M := mul_le_mul (entry_abs_le B i j) (hx j) (abs_nonneg _) (by norm_num)
        _ = M := one_mul M
    _ = _ := by simp [rowBase]

lemma trajectory_bound {n : ℕ} (B : Tournament n) (r : ℕ) (i : Fin n) :
    |trajectory (fun _ => B) (fun _ => (1:ℝ)) r i| ≤ rowBase n ^ r := by
  induction r generalizing i with
  | zero => simp [trajectory]
  | succ r ih =>
    have h := act_abs_le B (trajectory (fun _ => B) (fun _ => (1:ℝ)) r) (rowBase n ^ r) ih i
    simpa [trajectory, pow_succ', mul_comm] using h

lemma energy_bound (n r : ℕ) (B : Tournament n) :
    energy (matrix B) r ≤ (n : ℝ)*(rowBase n ^ r)^2 := by
  unfold energy
  calc
    _ ≤ ∑ _i : Fin n, (rowBase n ^ r)^2 := by
      apply sum_le_sum
      intro i hi
      have h := trajectory_bound B r i
      rw [trajectory_eq_mulVec] at h
      have hs := mul_self_le_mul_self (abs_nonneg ((matrix B^r).mulVec (fun _ => (1:ℝ)) i)) h
      simpa [← pow_two, sq_abs] using hs
    _ = _ := by simp

lemma source_bound (n r : ℕ) (B : Tournament n) (q : ℝ) (hq : 0 ≤ q) :
    q^r*energy (matrix B) (r+1) ≤ ((n : ℝ)*rowBase n ^2)*(q*rowBase n ^2)^r := by
  have h := mul_le_mul_of_nonneg_left (energy_bound n (r+1) B) (pow_nonneg hq r)
  have hp : ((rowBase n ^r)^2) = ((rowBase n ^2)^r) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  calc
    _ ≤ q^r*((n : ℝ)*(rowBase n ^(r+1))^2) := h
    _ = _ := by rw [pow_succ (rowBase n) r, mul_pow, hp, mul_pow]; ring

/-- Explicit row-sum domain, sharper than q*n²<1 and containing q=1/n². -/
theorem source_summable (n : ℕ) (B : Tournament n) (q : ℝ)
    (hq : 0 ≤ q) (hsmall : q*rowBase n ^2 < 1) :
    Summable (fun r : ℕ => q^r*energy (matrix B) (r+1)) := by
  have hg : Summable (fun r : ℕ => ((n : ℝ)*rowBase n ^2)*(q*rowBase n ^2)^r) :=
    (summable_geometric_of_lt_one (mul_nonneg hq (sq_nonneg _)) hsmall).mul_left _
  apply hg.of_nonneg_of_le
  · intro r
    apply mul_nonneg (pow_nonneg hq r)
    exact sum_nonneg (fun i hi => sq_nonneg _)
  · intro r
    exact source_bound n r B q hq

theorem source_series_le (n : ℕ) (B : Tournament n) (q : ℝ)
    (hq : 0 ≤ q) (hsmall : q*rowBase n ^2 < 1) :
    (∑' r : ℕ, q^r*energy (matrix B) (r+1)) ≤
      ∑' r : ℕ, q^r*energy (TransitiveOrbit.T n) (r+1) := by
  apply TournamentEnergySeries.source_series_le n B q hq
  · exact source_summable n B q hq hsmall
  · exact source_summable n (TransitiveOrbit.transitiveTournament n) q hq hsmall

lemma inverse_square_in_domain (n : ℕ) (hn : 0 < n) :
    (1/(n : ℝ)^2)*rowBase n ^2 < 1 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : rowBase n < (n : ℝ) := by
    unfold rowBase
    exact_mod_cast (show n-1 < n by omega)
  have hd0 : 0 ≤ rowBase n := by unfold rowBase; positivity
  have hs : rowBase n ^2 < (n : ℝ)^2 := by nlinarith
  rw [one_div_mul_eq_div]
  exact (div_lt_one (sq_pos_of_pos hp)).mpr hs

/-- The natural parameter q=1/n² is covered for every positive dimension. -/
theorem source_series_at_inverse_square (n : ℕ) (hn : 0 < n) (B : Tournament n) :
    (∑' r : ℕ, (1/(n : ℝ)^2)^r*energy (matrix B) (r+1)) ≤
      ∑' r : ℕ, (1/(n : ℝ)^2)^r*energy (TransitiveOrbit.T n) (r+1) := by
  exact source_series_le n B _ (by positivity) (inverse_square_in_domain n hn)
end TournamentEnergyRowDomain
#print axioms TournamentEnergyRowDomain.source_series_le
#print axioms TournamentEnergyRowDomain.source_series_at_inverse_square
