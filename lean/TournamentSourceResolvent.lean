import TournamentGramGeometric
import ResolventSeriesIdentity
noncomputable section
namespace TournamentSourceResolvent
open Finset Matrix VectorWeakMajorization TournamentPowerComparison TournamentEnergyRowDomain
open TournamentGramGeometric TournamentEnergySeries

def sourceResolvent {n : ℕ} (B : Tournament n) (q : ℝ) : ℝ :=
  dotProduct ((matrix B).mulVec (fun _ => (1:ℝ)))
    ((1+q • (matrix B ^2))⁻¹.mulVec ((matrix B).mulVec (fun _ => (1:ℝ))))

lemma normal_matrix {n : ℕ} (B : Tournament n) : Commute (matrix B).transpose (matrix B) := by
  rw [transpose_matrix]
  show (-(matrix B))*matrix B = matrix B*(-(matrix B))
  simp

lemma one_sub_C {n : ℕ} (B : Tournament n) (q : ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℝ)-C B q = 1+q • (matrix B ^2) := by
  unfold C TournamentGramGeometric.gram
  rw [transpose_matrix, neg_mul, ← pow_two, smul_neg, sub_neg_eq_add]

/-- The concrete resolvent matrix is genuinely invertible on the row domain. -/
theorem inverse_left_right {n : ℕ} (B : Tournament n) (q : ℝ)
    (hq : 0 ≤ q) (hsmall : q*rowBase n ^2 < 1) :
    (1+q • (matrix B ^2))⁻¹*(1+q • (matrix B ^2)) = 1 ∧
      (1+q • (matrix B ^2))*(1+q • (matrix B ^2))⁻¹ = 1 := by
  have h := ResolventSeriesIdentity.inverse_left_right (C B q) (geometric_summable B q hq hsmall)
  rw [one_sub_C] at h
  exact h

/-- Actual source resolvent = the proved convergent source-energy series.
No extra summability or invertibility hypothesis is imposed. -/
theorem resolvent_eq_series {n : ℕ} (B : Tournament n) (q : ℝ)
    (hq : 0 ≤ q) (hsmall : q*rowBase n ^2 < 1) :
    sourceResolvent B q = ∑' r : ℕ, q^r*energy (matrix B) (r+1) := by
  have h := ResolventSeriesIdentity.source_resolvent_eq_series (matrix B)
    (normal_matrix B) q (geometric_summable B q hq hsmall)
  change dotProduct ((matrix B).mulVec (fun _ => (1:ℝ)))
    ((1-C B q)⁻¹.mulVec ((matrix B).mulVec (fun _ => (1:ℝ)))) = _ at h
  rw [one_sub_C] at h
  exact h

/-- Genuine resolvent comparison, not merely a formal series inequality. -/
theorem source_resolvent_le {n : ℕ} (B : Tournament n) (q : ℝ)
    (hq : 0 ≤ q) (hsmall : q*rowBase n ^2 < 1) :
    sourceResolvent B q ≤ sourceResolvent (TransitiveOrbit.transitiveTournament n) q := by
  rw [resolvent_eq_series B q hq hsmall,
    resolvent_eq_series (TransitiveOrbit.transitiveTournament n) q hq hsmall]
  exact TournamentEnergyRowDomain.source_series_le n B q hq hsmall

/-- The natural q=1/n² parameter is included for every positive n. -/
theorem source_resolvent_natural (n : ℕ) (hn : 0 < n) (B : Tournament n) :
    sourceResolvent B (1/(n : ℝ)^2) ≤
      sourceResolvent (TransitiveOrbit.transitiveTournament n) (1/(n : ℝ)^2) := by
  exact source_resolvent_le B _ (by positivity) (inverse_square_in_domain n hn)
end TournamentSourceResolvent
#print axioms TournamentSourceResolvent.resolvent_eq_series
#print axioms TournamentSourceResolvent.source_resolvent_le
#print axioms TournamentSourceResolvent.source_resolvent_natural
