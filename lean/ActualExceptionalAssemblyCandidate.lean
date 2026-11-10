import ExceptionalFiniteMarginCandidate
import DeletedExceptionalFourBlockCandidate
import InducedSelectedAdapter
import SelectedPhysicalMinorBridge
import CoreMinorThresholdCandidate
import ActualMaximizerEntryCandidate

/-! Actual exceptional exclusion from independent core minors and the true
positive path convolution. All analytic gates are called, not assumed.
All thresholds are uniform in the actual tournament and deletion sets. -/
set_option autoImplicit false
noncomputable section
namespace ActualExceptionalAssemblyCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open InducedSelectedAdapter
open scoped Classical Topology
open Filter

/-- A common ambient threshold works for every induced core and both independent
row and column deletion sets. No monotonicity of error(core size) is used. -/
theorem actual_ambient_core_minors_eventually (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ)^2 * Real.log n →
      ∀ U : Finset (Fin n), U.card < subsetCutoff n →
      let F := exceptionalVertices T
      let M := (F ∪ U)ᶜ
      ∀ s ≤ F.card, ∀ I ∈ M.powersetCard (F.card-s), ∀ J ∈ M.powersetCard (F.card-s),
        selectedPermanent (adjacency T) (M \ J) (M \ I) ≤
          (2 * Real.exp (-1+eps) *
            (((M.card-(F.card-s)).factorial : ℝ)/(2 : ℝ)^(M.card-(F.card-s)))) *
            (∏ i ∈ I, ambientCoreLeft T M i) * (∏ j ∈ J, ambientCoreRight T M j) := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    (CoreMinorThresholdCandidate.eventually_core_minor.and
      (CoreMinorEnvelopeCandidate.error_tendsto.eventually_le_const heps))
  filter_upwards [short_deleted_exceptional_core_uniform_dense,
    eventually_ge_atTop (2*N0), eventually_ge_atTop (2 : ℕ)]
    with n hdense hnN hn T hV U hU
  dsimp only
  intro s hs I hI J hJ
  let F := exceptionalVertices T
  let M := (F ∪ U)ᶜ
  let S := inducedTournament T M
  obtain ⟨hM2,hMhalf,hcap,hτA,hτN⟩ := hdense T hV U hU
  have hN0M : N0 ≤ M.card := common_threshold hnN hMhalf
  have hactual := (hN0 M.card hN0M).1
  have herror := (hN0 M.card hN0M).2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hM0 : (0 : ℝ) < M.card := by exact_mod_cast (show 0 < M.card by dsimp [M,F]; omega)
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.log (M.card : ℝ) := by
    have h := Real.log_le_log hn0 (show (n : ℝ) ≤ 2*M.card by dsimp [M,F]; linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hM0.ne'] at h
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ M.card by exact_mod_cast hM2)
    linarith
  have hf := exceptionalVertices_card_le_log T hn hV
  have ht : ((F.card-s : ℕ) : ℝ) ≤ 800 * Real.log (M.card : ℝ) := by
    have hsf : ((F.card-s : ℕ) : ℝ) ≤ F.card := by exact_mod_cast Nat.sub_le F.card s
    dsimp [F] at hsf
    linarith
  have hIM : I ⊆ M := (Finset.mem_powersetCard.mp hI).1
  have hJM : J ⊆ M := (Finset.mem_powersetCard.mp hJ).1
  let P := localSet M I
  let Q := localSet M J
  have hP : P.card = F.card-s := (localSet_card M I hIM).trans (Finset.mem_powersetCard.mp hI).2
  have hQ : Q.card = F.card-s := (localSet_card M J hJM).trans (Finset.mem_powersetCard.mp hJ).2
  have hcP : Pᶜ.card = M.card-(F.card-s) := by simp only [Finset.card_compl, Fintype.card_fin,hP]
  have hcQ : Qᶜ.card = M.card-(F.card-s) := by simp only [Finset.card_compl, Fintype.card_fin,hQ]
  let r : Fin (M.card-(F.card-s)) ≃ ↥Pᶜ := (finCongr hcP.symm).trans (subsetVertexEquiv Pᶜ)
  let c : Fin (M.card-(F.card-s)) ≃ ↥Qᶜ := (finCongr hcQ.symm).trans (subsetVertexEquiv Qᶜ)
  have hp := hactual S (M.card-(F.card-s)) P Q r c hcap hτN (by simpa only [hP] using ht)
  rw [← SelectedPhysicalMinorBridge.selected_actual_eq_physical S P Q r c] at hp
  change selectedPermanent (adjacency (inducedTournament T M)) (localSet M J)ᶜ (localSet M I)ᶜ ≤ _ at hp
  rw [selected_induced_eq] at hp
  have hleft : (∏ i ∈ P, (1+normalizedScore S i)⁻¹) = ∏ i ∈ I, ambientCoreLeft T M i := by
    calc
      _ = ∏ i ∈ localSet M I, ambientCoreLeft T M (subsetVertexEquiv M i) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (ambientCoreLeft_equiv T M i).symm
      _ = _ := local_weight_product M I hIM (ambientCoreLeft T M)
  have hright : (∏ j ∈ Q, (1-normalizedScore S j)⁻¹) = ∏ j ∈ J, ambientCoreRight T M j := by
    calc
      _ = ∏ j ∈ localSet M J, ambientCoreRight T M (subsetVertexEquiv M j) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact (ambientCoreRight_equiv T M j).symm
      _ = _ := local_weight_product M J hJM (ambientCoreRight T M)
  rw [hleft,hright] at hp
  have hw := ambientCore_weights_nonneg T M (19/20) (by norm_num) (by norm_num) hcap
  have hl : 0 ≤ ∏ i ∈ I, ambientCoreLeft T M i := Finset.prod_nonneg (fun i _ => hw.1 i)
  have hr : 0 ≤ ∏ j ∈ J, ambientCoreRight T M j := Finset.prod_nonneg (fun j _ => hw.2 j)
  have he : 2 * Real.exp (-1+CoreMinorEnvelopeCandidate.error M.card) ≤
      2 * Real.exp (-1+eps) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  exact hp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (by positivity)) hl) hr)

/-- The actual remaining principal permanents are now bounded by the proved
independent core gate and weighted cross/four-block expansion. -/
theorem actual_remaining_permanents_eventually (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ)^2 * Real.log n →
      ∀ U : Finset (Fin n), U.card < subsetCutoff n → Disjoint U (exceptionalVertices T) →
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent ≤
        (2 * Real.exp (-1) * (1/4 : ℝ)^(exceptionalVertices T).card * Real.exp eps) *
          (((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card)) := by
  have heps2 : 0 < eps/2 := by linarith
  filter_upwards [actual_ambient_core_minors_eventually (eps/2) heps2,
    short_deleted_permanent_fourBlock_eventually,
    short_deleted_exceptional_core_uniform_dense,
    exceptional_assembly_error_eventually_small (eps/2) heps2,
    eventually_ge_atTop (2 : ℕ)] with n hcore hfour hdense herr hn T hV U hU hUF
  let F := exceptionalVertices T
  let M := (F ∪ U)ᶜ
  let B := 2 * Real.exp (-1+eps/2)
  have hp := hfour T hV U hU hUF B (by dsimp [B]; positivity) (hcore T hV U hU)
  have he := herr (F.card : ℝ) (M.card : ℝ) (by positivity)
    (exceptionalVertices_card_le_log T hn hV) (hdense T hV U hU).2.1
  have hb : B * (1/4 : ℝ)^F.card * Real.exp (292*(F.card : ℝ)^2/M.card) ≤
      B * (1/4 : ℝ)^F.card * Real.exp (eps/2) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by dsimp [B]; positivity)
  have heq : B * (1/4 : ℝ)^F.card * Real.exp (eps/2) =
      2 * Real.exp (-1) * (1/4 : ℝ)^F.card * Real.exp eps := by
    have hx : Real.exp (eps/2) * Real.exp (eps/2) = Real.exp eps := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = 2 * Real.exp (-1) * (1/4 : ℝ)^F.card *
          (Real.exp (eps/2) * Real.exp (eps/2)) := by
        dsimp [B]
        rw [Real.exp_add]
        ring
      _ = _ := by rw [hx]
  have hnorm := hp.trans (hb.trans_eq heq)
  exact (div_le_iff₀ (by positivity : 0 < ((n-U.card).factorial : ℝ)/(2 : ℝ)^(n-U.card))).mp hnorm

/-- Explicit absolute margin. The meeting term is only o(1); the true long
term is o(1/n), and neither one is divided by Gamma. -/
theorem actual_lowVariance_exceptional_eventually_le_191 :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      degreeVariance T < 16 * (n : ℝ)^2 * Real.log n →
      1 ≤ (exceptionalVertices T).card → (pathCount T : ℝ)/meanPaths n ≤ 191/200 := by
  let eps : ℝ := Real.log (21/20 : ℝ)/2
  have heps : 0 < eps := by dsimp [eps]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  filter_upwards [actual_remaining_permanents_eventually eps heps,
    convolution_cutoff_error_eventually_small eps heps,
    exceptional_meeting_convolution_eventually_small (1/25) (by norm_num),
    longConvolution_eventually_small (ε := 1/25) (by norm_num),
    deleted_exceptional_core_uniform_dense, short_cutoff_eventually_small,
    eventually_ge_atTop (2 : ℕ)] with n hper hcut hmeet hlong hgeom hshort hn T hV hF
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hK : 2 * subsetCutoff n ≤ n := by
    have hKR : 2 * (subsetCutoff n : ℝ) ≤ n := by linarith [hshort.2.1,hshort.2.2]
    exact_mod_cast hKR
  have hFlog := exceptionalVertices_card_le_log T hn hV
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hN : 0 < (exceptionalVertices T)ᶜ.card := by
    have hh := hgeom T hV (exceptionalVertices T) (Finset.Subset.refl _) (by linarith)
    omega
  have hE : Real.exp (eps+2*(subsetCutoff n : ℝ)^2/n) ≤ (21/20 : ℝ) := by
    apply (Real.exp_le_exp.mpr _).trans_eq (Real.exp_log (by norm_num))
    dsimp [eps] at hcut ⊢
    linarith
  have htail : longConvolution T (subsetCutoff n)/meanPaths n ≤ 1/25 := by
    apply (hlong T).trans
    apply (div_le_iff₀ hn0).mpr
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  exact exceptional_pathCount_le_191_of_crude_bound T (exceptionalVertices T) (subsetCutoff n)
    hnpos hK hN hF eps hE (hmeet T hV) htail (hper T hV)

/-- Actual maximizers enter the fixed cap. The only tournament input is the
actual maximizing equality; reference competition and low variance are internal. -/
theorem actual_maximizers_eventually_capped :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n, pathCount T = maxPaths n →
      exceptionalVertices T = ∅ ∧
      (∀ i, |normalizedScore T i| ≤ 9/10) ∧
      tau (normalizedScore T) ≤ 256*Real.log (n : ℝ) := by
  filter_upwards [actual_lowVariance_exceptional_eventually_le_191,
    ActualMaximizerEntryCandidate.actual_maximizers_eventually_lowVariance,
    ActualMaximizerEntryCandidate.maxPaths_eventually_ge_mean,
    eventually_ge_atTop (2 : ℕ)] with n hexcl hentry hmean hn T hmax
  have hlow := hentry T hmax
  have hF : exceptionalVertices T = ∅ := by
    by_contra hne
    have hf : 1 ≤ (exceptionalVertices T).card :=
      Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    have hbound := hexcl T hlow.1 hf
    have hm : 0 < meanPaths n := by unfold meanPaths; positivity
    have hcomp : 1 ≤ (pathCount T : ℝ)/meanPaths n := by
      apply (le_div_iff₀ hm).mpr
      simpa only [one_mul,hmax] using hmean
    linarith
  refine ⟨hF, ?_, hlow.2⟩
  intro i
  have hi : i ∉ exceptionalVertices T := by rw [hF]; simp
  have hraw := nonexceptional_score_le T i hi
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ)-1 := by linarith
  rw [normalizedScore,abs_div,abs_of_pos hden]
  exact (div_le_iff₀ hden).mpr hraw

end ActualExceptionalAssemblyCandidate

set_option pp.fullNames true
#check ActualExceptionalAssemblyCandidate.actual_ambient_core_minors_eventually
#print axioms ActualExceptionalAssemblyCandidate.actual_ambient_core_minors_eventually
#check ActualExceptionalAssemblyCandidate.actual_remaining_permanents_eventually
#print axioms ActualExceptionalAssemblyCandidate.actual_remaining_permanents_eventually
#check ActualExceptionalAssemblyCandidate.actual_lowVariance_exceptional_eventually_le_191
#print axioms ActualExceptionalAssemblyCandidate.actual_lowVariance_exceptional_eventually_le_191
#check ActualExceptionalAssemblyCandidate.actual_maximizers_eventually_capped
#print axioms ActualExceptionalAssemblyCandidate.actual_maximizers_eventually_capped
