import SmallDiamondComponentReduction
noncomputable section
open DiamondGap PivotCycleLink TriangleCountBridge SmallDiamondComponentReduction

/-- Independent graph endpoint with no supplied cycle count, link bound,
strong-block family, or component-size hypothesis. -/
theorem actual_small_diamond_component_bound {n : ℕ} (T : Tournament (Fin n))
    (hn : 4 ≤ n) (hD : 0 < T.diamonds.card)
    (hsmall : 24*T.diamonds.card ≤ n^2) :
    ∃ p : Fin n,
      (maxComponentSize (toReal (sourceSwitch T p)) : ℝ) ≤
        12*(T.diamonds.card : ℝ)/(n : ℝ) ∧
      2*maxComponentSize (toReal (sourceSwitch T p)) ≤ n :=
  exists_component_fraction_bound T hn hD hsmall
#print axioms actual_small_diamond_component_bound
#print axioms SmallDiamondComponentReduction.exists_small_components
#print axioms DiamondTriangleIncidence.diamonds_le_triangles
#print axioms TriangleCountBridge.ordered_eq_three_unordered
#print axioms PivotCycleLink.exists_pivot_total_cycles
#print axioms TournamentComponentBlocks.induced_strong
#print axioms TournamentComponentBlocks.component_size_le_cycleCount
#print axioms PivotMomentInvariant.sixth_eq
