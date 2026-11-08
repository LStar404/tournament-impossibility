import ReferenceOnesOrbit
noncomputable section
namespace TournamentEnergySeries
open Finset Matrix VectorWeakMajorization TournamentPowerComparison
open TournamentSwitching IteratedVectorMajorization ReferenceDiagonal

def energy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : ℝ :=
  ∑ i, ((A^r).mulVec (fun _ => (1:ℝ)) i)^2

lemma comparison_ones_norm (n r : ℕ) :
    (∑ i ∈ range n, (comparison n (sortedPad (fun _ : Fin n => (1:ℝ))) r i)^2) =
      energy (TransitiveOrbit.T n) r := by
  have hz : (fun j : Fin n => sortedPad (fun _ : Fin n => (1:ℝ)) j.val) = (fun _ => (1:ℝ)) := by
    funext j
    simp [sortedPad, j.isLt]
  calc
    _ = ∑ i : Fin n, (comparison n (sortedPad (fun _ : Fin n => (1:ℝ))) r i.val)^2 :=
      (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ i : Fin n, ((Kmatrix n ^ r).mulVec (fun _ => (1:ℝ)) i)^2 := by
      apply sum_congr rfl
      intro i hi
      rw [KMatrixIdentification.comparison_power, hz]
      rfl
    _ = _ := ReferenceOnesOrbit.ones_orbit_norm n r

/-- Source/all-one power energy comparison for actual tournaments. -/
theorem energy_le (n r : ℕ) (B : Tournament n) :
    energy (matrix B) r ≤ energy (TransitiveOrbit.T n) r := by
  have h := fixed_trajectory_sum_sq_le B (fun _ => (1:ℝ)) r
  simp only [trajectory_eq_mulVec] at h
  rw [comparison_ones_norm] at h
  exact h

/-- Every finite nonnegative spectral-moment combination is dominated. -/
theorem weighted_energy_le (n : ℕ) (B : Tournament n) (S : Finset ℕ)
    (w : ℕ → ℝ) (hw : ∀ r ∈ S, 0 ≤ w r) :
    (∑ r ∈ S, w r * energy (matrix B) r) ≤
      ∑ r ∈ S, w r * energy (TransitiveOrbit.T n) r := by
  apply sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left (energy_le n r B) (hw r hr)

/-- Truncated source-resolvent series coefficients. No inverse-matrix identity
or convergence assertion is hidden in this finite theorem. -/
theorem finite_source_series_le (n N : ℕ) (B : Tournament n) (q : ℝ) (hq : 0 ≤ q) :
    (∑ r ∈ range N, q^r * energy (matrix B) (r+1)) ≤
      ∑ r ∈ range N, q^r * energy (TransitiveOrbit.T n) (r+1) := by
  apply sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left (energy_le n (r+1) B) (pow_nonneg hq r)

/-- Infinite comparison only under explicit summability assumptions.
Establishing a spectral convergence domain and identifying a resolvent are
separate analytic tasks, not claimed by this theorem. -/
theorem source_series_le (n : ℕ) (B : Tournament n) (q : ℝ) (hq : 0 ≤ q)
    (hB : Summable (fun r : ℕ => q^r * energy (matrix B) (r+1)))
    (hT : Summable (fun r : ℕ => q^r * energy (TransitiveOrbit.T n) (r+1))) :
    (∑' r : ℕ, q^r * energy (matrix B) (r+1)) ≤
      ∑' r : ℕ, q^r * energy (TransitiveOrbit.T n) (r+1) := by
  apply hB.tsum_le_tsum _ hT
  intro r
  exact mul_le_mul_of_nonneg_left (energy_le n (r+1) B) (pow_nonneg hq r)
end TournamentEnergySeries
#print axioms TournamentEnergySeries.energy_le
#print axioms TournamentEnergySeries.finite_source_series_le
#print axioms TournamentEnergySeries.source_series_le
