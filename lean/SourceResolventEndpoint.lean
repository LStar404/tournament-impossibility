import TournamentSourceResolvent
open Matrix

/-- Raw-matrix endpoint with no assumed convergence, normality or invertibility. -/
theorem actual_source_resolvent_comparison (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i)
    (hunit : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1)
    (q : ℝ) (hq : 0 ≤ q) (hsmall : q*(((n-1 : ℕ) : ℝ)^2) < 1) :
    dotProduct (A.mulVec (fun _ => (1:ℝ)))
      ((1+q • (A^2))⁻¹.mulVec (A.mulVec (fun _ => (1:ℝ)))) ≤
    dotProduct ((TransitiveOrbit.T n).mulVec (fun _ => (1:ℝ)))
      ((1+q • ((TransitiveOrbit.T n)^2))⁻¹.mulVec
        ((TransitiveOrbit.T n).mulVec (fun _ => (1:ℝ)))) := by
  exact TournamentSourceResolvent.source_resolvent_le ⟨A,hskew,hunit⟩ q hq hsmall

#print axioms actual_source_resolvent_comparison
#print axioms TournamentSourceResolvent.inverse_left_right
#print axioms TournamentSourceResolvent.resolvent_eq_series
#print axioms TournamentSourceResolvent.source_resolvent_natural
