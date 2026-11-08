import OrdinalTournamentDeficit
import OrdinalTransitiveReference
noncomputable section
namespace OrdinalGlobalSixthDeficit
open Finset VectorWeakMajorization TournamentPowerComparison OrdinalTournamentDeficit

/-- Reference-normalized exact sixth deficit: the left reference is the single
actual transitive matrix of the total dimension. -/
theorem actual_formula (m : ℕ → ℕ) (B : ∀ i, Tournament (m i)) (k : ℕ) :
    TwoBlockSixthMoment.third (TransitiveOrbit.T (∑ i ∈ range k, m i))-
      TwoBlockSixthMoment.third (OrdinalBlockMatrix.matrix m (fun i => matrix (B i)) k) =
    SmallBlockSixthEstimate.deficit k (∑ i ∈ range k, (m i : ℝ))
      (fun i => (m i : ℝ)) (fun i => secondDeficit (B i))
      (fun i => sixthDeficit (B i)) (fun i => triangles (B i)) := by
  rw [← OrdinalTransitiveReference.sixth_eq m k]
  exact actual_deficit_formula m B k

/-- Actual sixth-moment lower bound. The size and D-versus-triangle inequalities
are the only remaining graph-specific hypotheses; no source/moment comparison
or triangle-total estimate is assumed. -/
theorem conditional_small (m : ℕ → ℕ) (B : ∀ i, Tournament (m i))
    (k : ℕ) (n h D : ℝ) (hnsize : ∑ i ∈ range k, (m i : ℝ) = n)
    (hn : 4 ≤ n) (hh : 0 ≤ h) (hhalf : 2*h ≤ n)
    (hm : ∀ i ∈ range k, (m i : ℝ) ≤ h)
    (hD : D ≤ (n-3)*(∑ i ∈ range k, triangles (B i))) :
    6*n^2*D ≤ TwoBlockSixthMoment.third (TransitiveOrbit.T (∑ i ∈ range k, m i))-
      TwoBlockSixthMoment.third (OrdinalBlockMatrix.matrix m (fun i => matrix (B i)) k) := by
  rw [← OrdinalTransitiveReference.sixth_eq m k]
  exact conditional_small_deficit m B k n h D hnsize hn hh hhalf hm hD
end OrdinalGlobalSixthDeficit
#print axioms OrdinalGlobalSixthDeficit.actual_formula
#print axioms OrdinalGlobalSixthDeficit.conditional_small
