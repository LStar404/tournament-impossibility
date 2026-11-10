import ActualPathConvolution
import TournamentSourceEnergy

/-!
Finite, unrestricted-deletion estimates for the *actual* tournament sign matrix.
No extremality, balanced tensor representation, fixed deletion size, or proxy
recovery hypothesis is used. These are upstream inputs to G1/G2, not proofs of
those global analytic entry theorems. Focused Lean checks are recorded alongside this file.
-/
noncomputable section
namespace ActualTournamentDeletionEnergy
open Finset
open TournamentHamiltonian

variable {n : ℕ}

def fullEnergy (T : Tournament n) : ℝ := ∑ i, (score T i)^2

def retainedScore (T : Tournament n) (U : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ j ∈ Uᶜ, signMatrix T i j

def deletedScore (T : Tournament n) (U : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ j ∈ U, signMatrix T i j

def retainedEnergy (T : Tournament n) (U : Finset (Fin n)) : ℝ :=
  ∑ i ∈ Uᶜ, (retainedScore T U i)^2

/-- Conversion to the existing real-sign tournament API preserves every edge. -/
def asRealTournament (T : Tournament n) : VectorWeakMajorization.Tournament n where
  entry := signMatrix T
  skew := signMatrix_skew T
  unit i j hij := by
    cases he : T.val i j <;> simp [signMatrix, hij, he]

@[simp] theorem energy_asRealTournament (T : Tournament n) :
    TournamentSourceEnergy.energy (asRealTournament T) = fullEnergy T := rfl

lemma sign_abs_le_one (T : Tournament n) (i j : Fin n) :
    |signMatrix T i j| ≤ 1 := by
  by_cases hij : i = j
  · simp [signMatrix, hij]
  · cases he : T.val i j <;> norm_num [signMatrix, hij, he]

lemma abs_partial_score_le_card (T : Tournament n) (U : Finset (Fin n)) (i : Fin n) :
    |∑ j ∈ U, signMatrix T i j| ≤ (U.card : ℝ) := by
  calc
    _ ≤ ∑ j ∈ U, |signMatrix T i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ U, (1 : ℝ) := sum_le_sum (fun j _ => sign_abs_le_one T i j)
    _ = _ := by simp

lemma abs_score_le_order (T : Tournament n) (i : Fin n) :
    |score T i| ≤ (n : ℝ) := by
  simpa [score] using abs_partial_score_le_card T univ i

lemma score_split (T : Tournament n) (U : Finset (Fin n)) (i : Fin n) :
    deletedScore T U i + retainedScore T U i = score T i := by
  exact sum_add_sum_compl U (fun j => signMatrix T i j)

lemma retained_score_eq (T : Tournament n) (U : Finset (Fin n)) (i : Fin n) :
    retainedScore T U i = score T i - deletedScore T U i := by
  linarith [score_split T U i]

lemma deleted_score_sq_le (T : Tournament n) (U : Finset (Fin n)) (i : Fin n) :
    (deletedScore T U i)^2 ≤ (U.card : ℝ)^2 := by
  have hb := abs_partial_score_le_card T U i
  have hs := mul_self_le_mul_self (abs_nonneg (deletedScore T U i)) hb
  simpa [deletedScore, ← pow_two, sq_abs] using hs

lemma fullEnergy_nonneg (T : Tournament n) : 0 ≤ fullEnergy T :=
  sum_nonneg (fun _ _ => sq_nonneg _)

lemma score_l1_le (T : Tournament n) :
    (∑ i, |score T i|) ≤ Real.sqrt ((n : ℝ) * fullEnergy T) := by
  apply Real.le_sqrt_of_sq_le
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n)))
    (f := fun i => |score T i|)
  simpa [fullEnergy, sq_abs] using h

/-- Every deletion size is allowed, including sizes depending on n. -/
theorem retainedEnergy_upper (T : Tournament n) (U : Finset (Fin n)) :
    retainedEnergy T U ≤ 2 * fullEnergy T +
      2 * ((Uᶜ).card : ℝ) * (U.card : ℝ)^2 := by
  have hsub : (∑ i ∈ Uᶜ, (score T i)^2) ≤ fullEnergy T := by
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
  calc
    retainedEnergy T U ≤ ∑ i ∈ Uᶜ,
        (2 * (score T i)^2 + 2 * (U.card : ℝ)^2) := by
      apply sum_le_sum
      intro i hi
      rw [retained_score_eq]
      have hb := deleted_score_sq_le T U i
      nlinarith [sq_nonneg (score T i + deletedScore T U i)]
    _ = 2 * (∑ i ∈ Uᶜ, (score T i)^2) +
        2 * ((Uᶜ).card : ℝ) * (U.card : ℝ)^2 := by
      simp [sum_add_distrib, ← mul_sum]
      ring
    _ ≤ _ := by linarith

/-- The G2 deletion-source estimate, with no pointwise bounded-score assumption.
The bound is O_L(n(k+1)^2), valid also when a score is O(sqrt n). -/
theorem linear_window_retainedEnergy (T : Tournament n) (U : Finset (Fin n))
    {L : ℝ} (hL : 0 ≤ L) (hE : fullEnergy T ≤ L * (n : ℝ)) :
    retainedEnergy T U ≤ 2 * (L + 1) * (n : ℝ) * ((U.card : ℝ) + 1)^2 := by
  have hu : ((Uᶜ).card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show (Uᶜ).card ≤ n by simpa using card_le_univ (Uᶜ))
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hk : 0 ≤ (U.card : ℝ) := Nat.cast_nonneg _
  have hb := retainedEnergy_upper T U
  have hku := mul_le_mul_of_nonneg_right hu (sq_nonneg (U.card : ℝ))
  have hpoly : L + (U.card : ℝ)^2 ≤ (L + 1) * ((U.card : ℝ) + 1)^2 := by
    nlinarith [mul_nonneg hL (sq_nonneg (U.card : ℝ)), mul_nonneg hL hk]
  have hm := mul_le_mul_of_nonneg_left hpoly hn
  nlinarith

lemma retained_square_lower (T : Tournament n) (U : Finset (Fin n)) (i : Fin n) :
    (score T i)^2 - 2 * (U.card : ℝ) * |score T i| ≤
      (retainedScore T U i)^2 := by
  rw [retained_score_eq]
  have hp : score T i * deletedScore T U i ≤
      (U.card : ℝ) * |score T i| := by
    calc
      _ ≤ |score T i * deletedScore T U i| := le_abs_self _
      _ = |score T i| * |deletedScore T U i| := abs_mul _ _
      _ ≤ |score T i| * (U.card : ℝ) :=
        mul_le_mul_of_nonneg_left (abs_partial_score_le_card T U i) (abs_nonneg _)
      _ = _ := mul_comm _ _
  nlinarith [sq_nonneg (deletedScore T U i)]

/-- Sharp deletion-energy lower bound used in G1's high-variance exclusion.
Writing V=E/4 recovers V(T-U) >= V(T)-k*n^2/4-k*sqrt(n*V(T)). -/
theorem retainedEnergy_lower (T : Tournament n) (U : Finset (Fin n)) :
    fullEnergy T - (U.card : ℝ) * (n : ℝ)^2 -
        2 * (U.card : ℝ) * Real.sqrt ((n : ℝ) * fullEnergy T) ≤
      retainedEnergy T U := by
  have hdel : (∑ i ∈ U, (score T i)^2) ≤ (U.card : ℝ) * (n : ℝ)^2 := by
    calc
      _ ≤ ∑ _i ∈ U, (n : ℝ)^2 := by
        apply sum_le_sum
        intro i hi
        have hs := mul_self_le_mul_self (abs_nonneg (score T i)) (abs_score_le_order T i)
        simpa [← pow_two, sq_abs] using hs
      _ = _ := by simp
  have hsplit : (∑ i ∈ U, (score T i)^2) +
      (∑ i ∈ Uᶜ, (score T i)^2) = fullEnergy T :=
    sum_add_sum_compl U (fun i => (score T i)^2)
  have hl1 : (∑ i ∈ Uᶜ, |score T i|) ≤ ∑ i, |score T i| :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => abs_nonneg _)
  have hcross := mul_le_mul_of_nonneg_left (hl1.trans (score_l1_le T))
    (show 0 ≤ 2 * (U.card : ℝ) by positivity)
  have hsum := sum_le_sum (s := Uᶜ) (fun i _ => retained_square_lower T U i)
  simp only [sum_sub_distrib, ← mul_sum] at hsum
  change (∑ i ∈ Uᶜ, (score T i)^2) -
    2 * (U.card : ℝ) * (∑ i ∈ Uᶜ, |score T i|) ≤ retainedEnergy T U at hsum
  linarith

/-- The energy above is literally the squared row-sum energy of the principal
submatrix, not a surrogate induced graph with an unspecified labelling. -/
theorem retainedEnergy_eq_submatrix (T : Tournament n) (U : Finset (Fin n)) :
    retainedEnergy T U =
      ∑ i : (Uᶜ : Finset (Fin n)),
        (∑ j : (Uᶜ : Finset (Fin n)),
          ((signMatrix T).submatrix Subtype.val Subtype.val) i j)^2 := by
  unfold retainedEnergy retainedScore
  rw [← Finset.sum_coe_sort (Uᶜ : Finset (Fin n))]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact (Finset.sum_coe_sort (Uᶜ : Finset (Fin n))
    (fun j => signMatrix T i.val j)).symm

end ActualTournamentDeletionEnergy
#print axioms ActualTournamentDeletionEnergy.retainedEnergy_upper
#print axioms ActualTournamentDeletionEnergy.linear_window_retainedEnergy
#print axioms ActualTournamentDeletionEnergy.retainedEnergy_lower
#print axioms ActualTournamentDeletionEnergy.retainedEnergy_eq_submatrix
