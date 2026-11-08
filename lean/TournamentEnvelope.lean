import SelectedSignPairs
import VectorWeakMajorization
namespace TournamentEnvelope
open Finset
variable {V : Type*} [DecidableEq V]

/-- Actual finite skew sign matrix on a finite ambient vertex set. -/
structure SignMatrix (U : Finset V) where
  entry : V → V → ℝ
  skew : ∀ i ∈ U, ∀ j ∈ U, entry i j = -entry j i
  bound : ∀ i ∈ U, ∀ j ∈ U, |entry i j| ≤ 1

/-- Every actual ±1 tournament from the earlier module is a SignMatrix. -/
def ofTournament {n : ℕ} (B : VectorWeakMajorization.Tournament n) :
    SignMatrix (univ : Finset (Fin n)) where
  entry := B.entry
  skew := by intro i hi j hj; exact B.skew i j
  bound := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j; simp [B.diagonal]
    · rcases B.unit i j hij with h | h <;> rw [h] <;> norm_num

/-- Pairing the internal selected-row sum uses only actual skew symmetry. -/
theorem internal_identity (U S : Finset V) (hS : S ⊆ U) (B : SignMatrix U)
    (x y : V → ℝ) :
    2 * (∑ i ∈ S, y i * (∑ j ∈ S, B.entry i j * x j)) =
      ∑ i ∈ S, ∑ j ∈ S, B.entry i j * (y i*x j-y j*x i) := by
  have hs : (∑ i ∈ S, ∑ j ∈ S, B.entry i j * (y j*x i)) =
      -(∑ i ∈ S, ∑ j ∈ S, B.entry i j * (y i*x j)) := by
    rw [sum_comm, ← sum_neg_distrib]
    apply sum_congr rfl; intro i hi
    rw [← sum_neg_distrib]
    apply sum_congr rfl; intro j hj
    rw [B.skew j (hS hj) i (hS hi)]; ring
  simp_rw [mul_sub, sum_sub_distrib]
  rw [hs]
  have he : (∑ i ∈ S, y i*(∑ j ∈ S, B.entry i j*x j)) =
      ∑ i ∈ S, ∑ j ∈ S, B.entry i j*(y i*x j) := by
    simp only [mul_sum]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj; ring
  rw [he]; ring

lemma edge_bound (a z : ℝ) (ha : |a| ≤ 1) : a*z ≤ |z| := by
  calc
    a*z ≤ |a*z| := le_abs_self _
    _ = |a| * |z| := abs_mul _ _
    _ ≤ 1*|z| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    _ = |z| := one_mul _

/-- A genuine selected-subset envelope for the real matrix row sum.
No hypothetical matrix-to-envelope inequality is assumed. -/
theorem selected_bound (U S : Finset V) (hS : S ⊆ U) (B : SignMatrix U)
    (x y : V → ℝ) (hy : ∀ i ∈ S, |y i| = 1)
    (hx : ∀ j ∈ U \ S, 0 ≤ x j) :
    (∑ i ∈ S, y i * (∑ j ∈ U, B.entry i j*x j)) ≤
      (S.card : ℝ)*(∑ j ∈ U \ S, x j) +
      (∑ i ∈ S, ∑ j ∈ S, |y i*x j-y j*x i|)/2 := by
  have hinternal :
      2*(∑ i ∈ S, y i*(∑ j ∈ S, B.entry i j*x j)) ≤
      ∑ i ∈ S, ∑ j ∈ S, |y i*x j-y j*x i| := by
    rw [internal_identity U S hS B x y]
    apply sum_le_sum; intro i hi
    apply sum_le_sum; intro j hj
    exact edge_bound _ _ (B.bound i (hS hi) j (hS hj))
  have houtside :
      (∑ i ∈ S, y i*(∑ j ∈ U \ S, B.entry i j*x j)) ≤
      (S.card : ℝ)*(∑ j ∈ U \ S, x j) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ U \ S, (y i*B.entry i j)*x j := by
        simp only [mul_sum, mul_assoc]
      _ ≤ ∑ i ∈ S, ∑ j ∈ U \ S, x j := by
        apply sum_le_sum; intro i hi
        apply sum_le_sum; intro j hj
        have hab : y i*B.entry i j ≤ 1 := by
          calc
            _ ≤ |y i*B.entry i j| := le_abs_self _
            _ = |B.entry i j| := by rw [abs_mul, hy i hi, one_mul]
            _ ≤ 1 := B.bound i (hS hi) j (mem_sdiff.mp hj).1
        simpa using mul_le_mul_of_nonneg_right hab (hx j hj)
      _ = _ := by simp
  have hsplit : (∑ i ∈ S, y i*(∑ j ∈ U, B.entry i j*x j)) =
      (∑ i ∈ S, y i*(∑ j ∈ S, B.entry i j*x j)) +
      (∑ i ∈ S, y i*(∑ j ∈ U \ S, B.entry i j*x j)) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl; intro i hi
    rw [← mul_add]
    congr 1
    simpa [add_comm] using (sum_sdiff hS (f := fun j => B.entry i j*x j)).symm
  rw [hsplit]
  linarith

/-- Exact conversion of symmetric double sums to the upper triangular sum. -/
theorem symmetric_square (F : ℕ → ℕ → ℝ)
    (hs : ∀ i j, F i j = F j i) (hd : ∀ i, F i i = 0) (n : ℕ) :
    (∑ i ∈ range n, ∑ j ∈ range n, F i j) =
      2*(∑ j ∈ range n, ∑ i ∈ range j, F i j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrec : (∑ i ∈ range (n+1), ∑ j ∈ range (n+1), F i j) =
        (∑ i ∈ range n, ∑ j ∈ range n, F i j) +
        (∑ i ∈ range n, F i n) + (∑ j ∈ range n, F n j) := by
      rw [sum_range_succ]
      simp_rw [sum_range_succ]
      rw [sum_add_distrib, hd n]
      ring
    have hsym : (∑ j ∈ range n, F n j) = ∑ i ∈ range n, F i n := by
      apply sum_congr rfl; intro i hi; exact hs n i
    rw [hrec, hsym, ih, sum_range_succ]
    ring

theorem abs_pair_square (s : ℕ → Bool) (b : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, ∑ j ∈ range n,
      |SelectedSignPairs.sign (s i)*b j-SelectedSignPairs.sign (s j)*b i|) =
      2*SelectedSignPairs.pairCost s b n := by
  apply symmetric_square
  · intro i j; exact abs_sub_comm _ _
  · intro i; simp


section Enumeration
variable [LinearOrder V]

lemma sum_enumeration (S : Finset V) (f : V → ℝ) :
    (∑ i ∈ S, f i) = ∑ i : Fin S.card, f (S.orderEmbOfFin rfl i) := by
  rw [← sum_coe_sort]
  exact (Equiv.sum_comp (S.orderIsoOfFin rfl).toEquiv (fun i : S => f i)).symm

/-- Zero extension of values along the canonical increasing enumeration. -/
def enumerated (S : Finset V) (f : V → ℝ) (j : ℕ) : ℝ :=
  if hj : j < S.card then f (S.orderEmbOfFin rfl ⟨j,hj⟩) else 0

lemma sum_enumerated (S : Finset V) (f : V → ℝ) :
    (∑ i ∈ S, f i) = ∑ j ∈ range S.card, enumerated S f j := by
  rw [sum_enumeration]
  have he : (∑ i : Fin S.card, f (S.orderEmbOfFin rfl i)) =
      ∑ i : Fin S.card, enumerated S f i := by
    apply sum_congr rfl; intro i hi
    simp [enumerated, i.isLt]
  rw [he, Fin.sum_univ_eq_sum_range]

def enumeratedSign (S : Finset V) (t : V → Bool) (j : ℕ) : Bool :=
  if hj : j < S.card then t (S.orderEmbOfFin rfl ⟨j,hj⟩) else false

/-- The selected double absolute sum is exactly twice the enumerated pairCost. -/
theorem selected_pairCost (S : Finset V) (t : V → Bool) (x : V → ℝ) :
    (∑ i ∈ S, ∑ j ∈ S,
      |SelectedSignPairs.sign (t i)*x j-SelectedSignPairs.sign (t j)*x i|) =
      2*SelectedSignPairs.pairCost (enumeratedSign S t) (enumerated S x) S.card := by
  rw [sum_enumeration]
  have he : (∑ i : Fin S.card, ∑ j ∈ S,
      |SelectedSignPairs.sign (t (S.orderEmbOfFin rfl i))*x j-
        SelectedSignPairs.sign (t j)*x (S.orderEmbOfFin rfl i)|) =
      ∑ i : Fin S.card, ∑ j : Fin S.card,
      |SelectedSignPairs.sign (enumeratedSign S t i)*enumerated S x j-
        SelectedSignPairs.sign (enumeratedSign S t j)*enumerated S x i| := by
    apply sum_congr rfl; intro i hi
    rw [sum_enumeration]
    apply sum_congr rfl; intro j hj
    simp [enumeratedSign, enumerated, i.isLt, j.isLt]
  rw [he]
  have hfin (F : ℕ → ℕ → ℝ) :
      (∑ i : Fin S.card, ∑ j : Fin S.card, F i.val j.val) =
      ∑ i ∈ range S.card, ∑ j ∈ range S.card, F i j := by
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin S.card, F i j.val)]
    apply sum_congr rfl
    intro i hi
    exact Fin.sum_univ_eq_sum_range (F i) S.card
  rw [hfin (fun i j => |SelectedSignPairs.sign (enumeratedSign S t i)*enumerated S x j-
    SelectedSignPairs.sign (enumeratedSign S t j)*enumerated S x i|)]
  exact abs_pair_square _ _ _

/-- Actual selected matrix row bound with the exact internal pairCost,
using the canonical increasing enumeration of the selected vertices. -/
theorem selected_bound_pairCost (U S : Finset V) (hS : S ⊆ U) (B : SignMatrix U)
    (x : V → ℝ) (t : V → Bool) (hx : ∀ j ∈ U \ S, 0 ≤ x j) :
    (∑ i ∈ S, SelectedSignPairs.sign (t i)*(∑ j ∈ U, B.entry i j*x j)) ≤
      (S.card : ℝ)*(∑ j ∈ U \ S, x j) +
      SelectedSignPairs.pairCost (enumeratedSign S t) (enumerated S x) S.card := by
  have hy : ∀ i ∈ S, |SelectedSignPairs.sign (t i)| = 1 := by
    intro i hi; cases t i <;> norm_num [SelectedSignPairs.sign]
  have hh := selected_bound U S hS B x (fun i => SelectedSignPairs.sign (t i)) hy hx
  rw [selected_pairCost] at hh
  linarith

end Enumeration

end TournamentEnvelope
#print axioms TournamentEnvelope.selected_bound

#print axioms TournamentEnvelope.abs_pair_square

#print axioms TournamentEnvelope.selected_bound_pairCost
