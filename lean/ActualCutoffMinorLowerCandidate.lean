import ActualUnitMinorLowerCandidate
import GeneralScoreLowerConvolutionFocused
set_option autoImplicit false
noncomputable section
namespace ActualCutoffMinorLowerCandidate
open Filter
open scoped Topology
open TournamentHamiltonian UnitMinorErrorBudgetCandidate ActualUnitMinorLowerCandidate

/-- Exact hper shape consumed by the positive principal convolution. -/
theorem eventually_cutoff_signed_minor_lower :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n), (∀ i, |score T i|≤1) →
      ∀ U : Finset (Fin n), U.card<subsetCutoff n →
      Real.exp (-1)*gaussianFactor T*(((n-U.card).factorial:ℝ)/(2:ℝ)^(n-U.card))*
        (1-UnitMinorErrorBudgetCandidate.lowerConstant*((U.card:ℝ)+2)^2/(n:ℝ)) ≤
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n))→Fin n) Subtype.val).permanent := by
  have hcut := cutoff_div_log_tendsto.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_actual_signed_minor_lower,
    hcut.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)), eventually_gt_atTop 1]
    with n hp hc hn
  intro T hs U hU
  have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hcb : (subsetCutoff n:ℝ)≤Real.log (n:ℝ) := by
    have hh := (div_lt_iff₀ hln).mp hc
    simpa only [subsetCutoff, one_mul] using hh.le
  have ht : (U.card:ℝ)≤Real.log (n:ℝ) :=
    (show (U.card:ℝ)≤(subsetCutoff n:ℝ) by exact_mod_cast hU.le).trans hcb
  have hcard : Fintype.card (Uᶜ : Finset (Fin n))=n-U.card := by simp
  exact hp T (n-U.card) U (Fintype.equivFinOfCardEq hcard).symm hs ht
end ActualCutoffMinorLowerCandidate
