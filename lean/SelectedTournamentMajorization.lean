import TournamentEnvelope
import SelectedRowOptimization
import TopAbsoluteSelection
noncomputable section
namespace SelectedTournamentMajorization
open Finset VectorWeakMajorization MajorizationCone TournamentEnvelope

/-- Actual signed selection bound for a nonnegative decreasing input. -/
theorem selected_signed_le {n : ℕ} (B : Tournament n) (x : ℕ → ℝ)
    (hx : ∀ i < n, 0 ≤ x i)
    (hanti : ∀ a b, a ≤ b → b < n → x b ≤ x a)
    (S : Finset (Fin n)) (t : Fin n → Bool) :
    (∑ i ∈ S, SelectedSignPairs.sign (t i) * B.act (fun j => x j.val) i) ≤
      P n S.card x := by
  let k := S.card
  have hk : k ≤ n := by simpa [k] using (card_le_univ S)
  let f : ℕ → ℕ := fun j => if hj : j < k then (S.orderEmbOfFin rfl ⟨j,hj⟩).val else n
  let b := enumerated S (fun i : Fin n => x i.val)
  have hr : ∀ j < k, f j < n := by
    intro j hj
    simp only [f, dif_pos hj]
    exact (S.orderEmbOfFin rfl ⟨j,hj⟩).isLt
  have hf : ∀ j, j+1 < k → f j < f (j+1) := by
    intro j hj
    have hji : j < k := by omega
    simp only [f, dif_pos hj, dif_pos hji]
    exact (S.orderEmbOfFin rfl).strictMono (show (⟨j,hji⟩ : Fin k) < ⟨j+1,hj⟩ by exact Nat.lt_succ_self j)
  have hsel : ∀ j < k, b j = x (f j) := by
    intro j hj
    have hjs : j < S.card := hj
    simp [b, enumerated, f, hj, hjs]
  have hd : ∀ i j, i < j → j < k → b j ≤ b i := by
    intro i j hij hj
    have hi : i < k := by omega
    rw [hsel i hi, hsel j hj]
    apply hanti _ _ _ (hr j hj)
    simp only [f, dif_pos hi, dif_pos hj]
    exact (S.orderEmbOfFin rfl).monotone (show (⟨i,hi⟩ : Fin k) ≤ ⟨j,hj⟩ by exact Nat.le_of_lt hij)
  have hb : DescendingNonnegative k b := by
    constructor
    · intro j hj
      by_cases hjk : j < k
      · rw [hsel j hjk]; exact hx _ (hr j hjk)
      · simp [b, enumerated, show ¬ j < S.card from hjk]
    · intro j hj
      by_cases hjk : j+1 < k
      · exact hd j (j+1) (by omega) hjk
      · have hz : b (j+1) = 0 := by simp [b, enumerated, show ¬ j+1 < S.card from hjk]
        rw [hz, hsel j hj]
        exact hx _ (hr j hj)
  have henv := SelectedRowOptimization.envelope_le_P n k hk f hf hr x b
    (enumeratedSign S t) hanti hb hd hsel
  have hmat := selected_bound_pairCost (univ : Finset (Fin n)) S
    (subset_univ S) (ofTournament B) (fun i => x i.val) t
    (fun j _ => hx j.val j.isLt)
  have htot : (∑ i : Fin n, x i.val) = ∑ i ∈ range n, x i :=
    Fin.sum_univ_eq_sum_range x n
  have hselSum : (∑ i ∈ S, x i.val) = ∑ j ∈ range k, b j :=
    sum_enumerated S (fun i => x i.val)
  have hcomp : (∑ i ∈ (univ : Finset (Fin n)) \ S, x i.val) =
      (∑ i ∈ range n, x i) - ∑ j ∈ range k, b j := by
    rw [sum_sdiff_eq_sub (subset_univ S), htot, hselSum]
  rw [hcomp] at hmat
  change (∑ i ∈ S, SelectedSignPairs.sign (t i) * B.act (fun j => x j.val) i) ≤ _ at hmat
  exact le_trans hmat henv


lemma boolSign_eq (a : ℝ) : SelectedSignPairs.sign (decide (0 ≤ a)) = TournamentSwitching.sign a := by
  simp [SelectedSignPairs.sign, TournamentSwitching.sign]

/-- Largest absolute output prefixes are obtained by an actual selected set. -/
theorem sorted_input_majorization {n : ℕ} (B : Tournament n) (x : ℕ → ℝ)
    (hx : ∀ i < n, 0 ≤ x i)
    (hanti : ∀ a b, a ≤ b → b < n → x b ≤ x a) :
    WeakMajorized n (TournamentSwitching.sortedPad (B.act (fun j => x j.val))) (K n x) := by
  intro k hk
  let out := B.act (fun j => x j.val)
  let S := TopAbsoluteSelection.topSet out k hk
  let t : Fin n → Bool := fun i => decide (0 ≤ out i)
  have hh := selected_signed_le B x hx hanti S t
  have hc : S.card = k := TopAbsoluteSelection.card_topSet out k hk
  rw [hc] at hh
  have he : (∑ i ∈ S, SelectedSignPairs.sign (t i) * B.act (fun j => x j.val) i) =
      prefixSum (TournamentSwitching.sortedPad out) k := by
    change (∑ i ∈ S, SelectedSignPairs.sign (decide (0 ≤ out i)) * out i) = _
    simp only [boolSign_eq]
    exact TopAbsoluteSelection.signed_topSet out k hk
  rw [he] at hh
  rw [prefix_K n k hk]
  exact hh

/-- Complete finite vector weak majorization for every actual tournament and
arbitrary real input. K is defined by the proved exact P-difference formula. -/
theorem tournament_vector_majorization {n : ℕ} (B : Tournament n) (x : Fin n → ℝ) :
    WeakMajorized n (TournamentSwitching.sortedPad (B.act x))
      (K n (TournamentSwitching.sortedPad x)) := by
  let xp := TournamentSwitching.sortedPad x
  let Bp := TournamentSwitching.switched B (TournamentSwitching.absSort x) x
  have hx : ∀ i < n, 0 ≤ xp i := by
    intro i hi
    exact (TournamentSwitching.sortedPad_cone x).1 i (Nat.le_of_lt hi)
  have hanti : ∀ a b, a ≤ b → b < n → xp b ≤ xp a := by
    intro a b hab hb
    have ha : a < n := lt_of_le_of_lt hab hb
    simp only [xp, TournamentSwitching.sortedPad, dif_pos ha, dif_pos hb]
    exact TournamentSwitching.absSort_antitone x
      (show (⟨a,ha⟩ : Fin n) ≤ ⟨b,hb⟩ from hab)
  have hh := sorted_input_majorization Bp xp hx hanti
  rw [TournamentSwitching.normalized_sorted_output B x] at hh
  exact hh


/-- Expanded endpoint: no opaque abstract majorization predicate or K on the
right side, just the explicit tournament-selected-tail inequality. -/
theorem tournament_prefix_bound {n : ℕ} (B : Tournament n) (x : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ range k, TournamentSwitching.sortedPad (B.act x) i) ≤
      (k : ℝ) * (∑ i ∈ range n, TournamentSwitching.sortedPad x i) -
      ∑ j ∈ range k, (penalty j : ℝ) * TournamentSwitching.sortedPad x (n-k+j) := by
  have h := tournament_vector_majorization B x k hk
  rw [prefix_K n k hk, P_tail_formula n k hk] at h
  exact h

end SelectedTournamentMajorization

#print axioms SelectedTournamentMajorization.tournament_vector_majorization

#print axioms SelectedTournamentMajorization.tournament_prefix_bound
