import OrdinalGlobalSixthDeficit
noncomputable section
open Finset Matrix VectorWeakMajorization TournamentPowerComparison
open OrdinalTournamentDeficit

/-- Expanded full-dimension reference and actual block-matrix sixth norms. -/
theorem global_sixth_deficit_expanded (m : ℕ → ℕ)
    (B : ∀ i, Tournament (m i)) (k : ℕ) :
    (∑ i, ∑ j, (((TransitiveOrbit.T (∑ a ∈ range k, m a))^3) i j)^2)-
    (∑ i, ∑ j, (((OrdinalBlockMatrix.matrix m (fun a => matrix (B a)) k)^3) i j)^2) =
    (∑ i ∈ range k, sixthDeficit (B i))+
      6*(∑ i ∈ range k, ((∑ a ∈ range k, (m a : ℝ))-(m i : ℝ))*secondDeficit (B i))+
      16*(∑ i ∈ range k,
        ((∑ a ∈ range k, (m a : ℝ))^3-
          3*(∑ a ∈ range k, (m a : ℝ))*(m i : ℝ)^2+
          2*(m i : ℝ)^3-(∑ a ∈ range k, (m a : ℝ))+(m i : ℝ))*
        ((TournamentSourceEnergy.cycleCount (B i) : ℝ)/3))-
      384*(∑ i ∈ range k, ∑ j ∈ range i,
        ((TournamentSourceEnergy.cycleCount (B j) : ℝ)/3)*
        ((TournamentSourceEnergy.cycleCount (B i) : ℝ)/3)) := by
  simpa only [SmallBlockSixthEstimate.deficit, OrdinalSixthPolynomial.pairInteraction,
    triangles, TwoBlockSixthMoment.third, RectangularFrobenius.sqnorm,
    RectangularFrobenius.inner, pow_two] using OrdinalGlobalSixthDeficit.actual_formula m B k
#print axioms global_sixth_deficit_expanded
#print axioms OrdinalGlobalSixthDeficit.conditional_small
#print axioms TournamentSourceEnergy.first_eq_reference_sub
#print axioms TransitiveFirstEnergy.first_closed_form
