import VectorWeakMajorization
noncomputable section
namespace TournamentSwitching
open Finset VectorWeakMajorization

def sign (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1
lemma sign_sq (a : ℝ) : sign a * sign a = 1 := by
  unfold sign; split_ifs <;> norm_num
lemma sign_abs (a : ℝ) : |sign a| = 1 := by
  unfold sign; split_ifs <;> norm_num
lemma sign_mul (a : ℝ) : sign a * a = |a| := by
  unfold sign
  split_ifs with h
  · simpa using (abs_of_nonneg h).symm
  · simpa using (abs_of_neg (lt_of_not_ge h)).symm
lemma sign_mul_abs (a : ℝ) : sign a * |a| = a := by
  rw [← sign_mul, ← mul_assoc, sign_sq, one_mul]

def switched {n : ℕ} (B : Tournament n) (p : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) : Tournament n where
  entry i j := sign (x (p i)) * sign (x (p j)) * B.entry (p i) (p j)
  skew i j := by rw [B.skew (p i) (p j)]; ring
  unit i j hij := by
    have hne : p i ≠ p j := fun h => hij (p.injective h)
    rcases B.unit (p i) (p j) hne with h | h
    all_goals unfold sign; split_ifs <;> simp [h]

/-- Signed permutation changes arbitrary input to permuted absolute input. -/
theorem switched_act {n : ℕ} (B : Tournament n) (p : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (i : Fin n) :
    (switched B p x).act (fun j => |x (p j)|) i =
      sign (x (p i)) * B.act x (p i) := by
  simp only [Tournament.act, switched]
  rw [mul_sum]
  have he : (∑ j, sign (x (p i)) * sign (x (p j)) * B.entry (p i) (p j) * |x (p j)|) =
      ∑ j, sign (x (p i)) * (B.entry (p i) (p j) * x (p j)) := by
    apply sum_congr rfl
    intro j hj
    calc
      _ = sign (x (p i)) * B.entry (p i) (p j) * (sign (x (p j)) * |x (p j)|) := by ring
      _ = _ := by rw [sign_mul_abs]; ring
  rw [he]
  exact Equiv.sum_comp p (fun j => sign (x (p i)) * (B.entry (p i) j * x j))

theorem abs_switched_act {n : ℕ} (B : Tournament n) (p : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (i : Fin n) :
    |(switched B p x).act (fun j => |x (p j)|) i| = |B.act x (p i)| := by
  rw [switched_act, abs_mul, sign_abs, one_mul]

/-- A genuine sorting permutation, with stable ties supplied by Mathlib. -/
def absSort {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => -|x i|)

theorem absSort_antitone {n : ℕ} (x : Fin n → ℝ) :
    Antitone (fun i => |x (absSort x i)|) := by
  intro i j hij
  have h := Tuple.monotone_sort (fun i => -|x i|) hij
  change -|x (absSort x i)| ≤ -|x (absSort x j)| at h
  linarith

def sortedPad {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then |x (absSort x ⟨i, hi⟩)| else 0

theorem sortedPad_cone {n : ℕ} (x : Fin n → ℝ) :
    DescendingNonnegative n (sortedPad x) := by
  constructor
  · intro i hi
    unfold sortedPad
    split_ifs <;> positivity
  · intro i hi
    by_cases hn : i+1 < n
    · simp only [sortedPad, dif_pos hi, dif_pos hn]
      exact absSort_antitone x (show (⟨i, hi⟩ : Fin n) ≤ ⟨i+1, hn⟩ by exact Nat.le_succ i)
    · simp only [sortedPad, dif_pos hi, dif_neg hn]
      exact abs_nonneg _

theorem sortedPad_endpoint {n : ℕ} (x : Fin n → ℝ) : sortedPad x n = 0 := by
  simp [sortedPad]

/-- Arbitrary real input is reduced to sorted nonnegative input using an actual
switched tournament; absolute output entries are merely permuted. -/
theorem normalized_output {n : ℕ} (B : Tournament n) (x : Fin n → ℝ)
    (i : Fin n) :
    |(switched B (absSort x) x).act (fun j => sortedPad x j.val) i| =
      |B.act x (absSort x i)| := by
  have he : (fun j : Fin n => sortedPad x j.val) =
      (fun j : Fin n => |x (absSort x j)|) := by
    funext j
    simp [sortedPad, j.isLt]
  rw [he]
  exact abs_switched_act B (absSort x) x i


/-- Sorting removes any permutation of the input coordinates. -/
theorem sortedPad_perm {n : ℕ} (x : Fin n → ℝ) (p : Equiv.Perm (Fin n)) :
    sortedPad (fun i => x (p i)) = sortedPad x := by
  funext i
  by_cases hi : i < n
  · simp only [sortedPad, dif_pos hi]
    have he := congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort
      (f := fun j => -|x j|) (σ := p)) (⟨i, hi⟩ : Fin n)
    change -|x (p (absSort (fun j => x (p j)) ⟨i, hi⟩))| =
      -|x (absSort x ⟨i, hi⟩)| at he
    linarith
  · simp [sortedPad, hi]

/-- Only absolute input coordinates affect their absolute sorted tuple. -/
theorem sortedPad_abs_congr {n : ℕ} (x y : Fin n → ℝ)
    (h : ∀ i, |x i| = |y i|) : sortedPad x = sortedPad y := by
  have he : (fun i => -|x i|) = (fun i => -|y i|) := by
    funext i; rw [h]
  have hp : absSort x = absSort y := by unfold absSort; rw [he]
  funext i
  by_cases hi : i < n
  · simp only [sortedPad, dif_pos hi, hp]
    exact h _
  · simp [sortedPad, hi]

/-- The full sorted absolute output, not merely its multiset, is unchanged. -/
theorem normalized_sorted_output {n : ℕ} (B : Tournament n) (x : Fin n → ℝ) :
    sortedPad ((switched B (absSort x) x).act (fun j => sortedPad x j.val)) =
      sortedPad (B.act x) := by
  calc
    _ = sortedPad (fun i => B.act x (absSort x i)) :=
      sortedPad_abs_congr _ _ (normalized_output B x)
    _ = _ := sortedPad_perm (B.act x) (absSort x)

end TournamentSwitching
#print axioms TournamentSwitching.switched_act
#print axioms TournamentSwitching.abs_switched_act

#print axioms TournamentSwitching.normalized_output
#print axioms TournamentSwitching.sortedPad_cone

#print axioms TournamentSwitching.normalized_sorted_output
