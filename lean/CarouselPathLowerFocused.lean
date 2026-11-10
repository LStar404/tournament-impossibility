import TournamentHamiltonian.SkewSpectrum

/-! Static two-declaration extraction from the upstream CarouselPathLower.
The spectral existence proof is preserved verbatim. The maxPaths wrapper is
adapted to expose the missing all-unit-score path lower bound as hUnitLower.
No import or claim of an unconditional unit-score path estimate is made. -/
namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem exists_unit_score_spectral_near_lower_constant :
    ∃ C : ℝ,0≤C ∧ ∃ N : ℕ,1≤N ∧ ∀ n : ℕ,N≤n →
      ∃ T : Tournament n,(∀ i,|score T i|≤1) ∧ |spectralRatio T-lowerConstant|≤C/n := by
  obtain ⟨C,hC,N,hN,hbound⟩ := carousel_spectralRatios_error_bound
  refine ⟨C,hC,N,hN,?_⟩
  intro n hn
  rcases Nat.even_or_odd n with ⟨m,he⟩|⟨m,ho⟩
  · have heq : n=2*m := by omega
    rcases heq with rfl
    refine ⟨evenCarouselTournament m,?_,?_⟩
    · intro i
      exact (evenCarouselTournament_score m i).le
    · simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbound m).2 hn
  · subst n
    refine ⟨carouselTournament m,?_,?_⟩
    · intro i
      rw [carouselTournament_score]
      norm_num
    · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using (hbound m).1 hn

/-- Conditional reduction only. The all-unit-score path lower estimate is
an explicit input; this theorem does not prove or assume it silently. -/
theorem maxPaths_lower_uniform_of_unit_score
    (hUnitLower : ∃ Cp : ℝ, 0 ≤ Cp ∧ ∃ Np : ℕ, 2 ≤ Np ∧
      ∀ n : ℕ, Np ≤ n → ∀ T : Tournament n, (∀ i, |score T i| ≤ 1) →
        spectralRatio T-Cp/n ≤ (pathCount T : ℝ)/meanPaths n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (lowerConstant-C/n)*meanPaths n ≤ (maxPaths n : ℝ) := by
  obtain ⟨Cs, hCs, Ns, _hNs, hs⟩ := exists_unit_score_spectral_near_lower_constant
  obtain ⟨Cp, hCp, Np, hNp, hp⟩ := hUnitLower
  refine ⟨Cs+Cp, add_nonneg hCs hCp, max Ns Np, by omega, ?_⟩
  intro n hn
  have hnNs : Ns ≤ n := by omega
  have hnNp : Np ≤ n := by omega
  obtain ⟨T, hscore, hnear⟩ := hs n hnNs
  have hpath := hp n hnNp T hscore
  have hmean : 0 < meanPaths n := by unfold meanPaths; positivity
  have hspec := (abs_le.mp hnear).1
  have hnorm : lowerConstant-(Cs+Cp)/n ≤ (pathCount T : ℝ)/meanPaths n := by
    have he : (Cs+Cp)/(n : ℝ) = Cs/n+Cp/n := by ring
    rw [he]
    linarith
  have hcount := (le_div_iff₀ hmean).mp hnorm
  exact hcount.trans (by exact_mod_cast pathCount_le_maxPaths T)

end TournamentHamiltonian
