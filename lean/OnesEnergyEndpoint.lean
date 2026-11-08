import TournamentEnergyRowDomain
open Finset

/-- Independent source-energy endpoint with raw matrix entry assumptions. -/
theorem actual_source_power_energy (n r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i)
    (hunit : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1) :
    (∑ i, ((A^r).mulVec (fun _ => (1:ℝ)) i)^2) ≤
      ∑ i, ((TransitiveOrbit.T n ^ r).mulVec (fun _ => (1:ℝ)) i)^2 := by
  exact TournamentEnergySeries.energy_le n r ⟨A, hskew, hunit⟩

theorem actual_source_series_small (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i)
    (hunit : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1)
    (q : ℝ) (hq : 0 ≤ q) (hsmall : q*(n : ℝ)^2 < 1) :
    (∑' r : ℕ, q^r*(∑ i, ((A^(r+1)).mulVec (fun _ => (1:ℝ)) i)^2)) ≤
      ∑' r : ℕ, q^r*(∑ i, ((TransitiveOrbit.T n ^ (r+1)).mulVec (fun _ => (1:ℝ)) i)^2) := by
  exact TournamentEnergyConvergence.source_series_le_small n ⟨A,hskew,hunit⟩ q hq hsmall

#print axioms actual_source_power_energy
#print axioms actual_source_series_small
#print axioms ReferenceOnesOrbit.Q_ones_shift
#print axioms ReferenceOnesOrbit.ones_orbit_norm

/-- The natural q=1/n² point is included, with convergence proved internally. -/
theorem actual_source_series_natural (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i)
    (hunit : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1) :
    (∑' r : ℕ, (1/(n : ℝ)^2)^r*(∑ i, ((A^(r+1)).mulVec (fun _ => (1:ℝ)) i)^2)) ≤
      ∑' r : ℕ, (1/(n : ℝ)^2)^r*(∑ i, ((TransitiveOrbit.T n ^ (r+1)).mulVec (fun _ => (1:ℝ)) i)^2) := by
  exact TournamentEnergyRowDomain.source_series_at_inverse_square n hn ⟨A,hskew,hunit⟩

#print axioms actual_source_series_natural
