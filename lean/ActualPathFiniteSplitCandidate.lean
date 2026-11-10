import ActualReconstructionBridgeCandidate
import TournamentHamiltonian.PathConvolutionGenerating
set_option autoImplicit false
noncomputable section
namespace ActualPathFiniteSplitCandidate
open Matrix Finset TournamentHamiltonian
variable {n : ℕ}

lemma physical_adjacency_eq (T : Tournament n) :
    ActualReconstructionBridgeCandidate.adjacency T = TournamentHamiltonian.adjacency T := by
  ext i j
  have hh := twice_adjacency T i j
  unfold ActualReconstructionBridgeCandidate.adjacency
  nlinarith

def term (T : Tournament n) (U : Finset (Fin n)) : ℝ :=
  (principalWeightMatrix T U).det *
    ((TournamentHamiltonian.adjacency T).submatrix
      (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent

lemma term_nonneg (T : Tournament n) (U : Finset (Fin n)) : 0 ≤ term T U :=
  mul_nonneg (principal_weight_pos T U).le (adjacency_principal_permanent_nonneg T Uᶜ)

lemma actual_short_tail_split (T : Tournament n) (K : ℕ) :
    (pathCount T : ℝ) =
      (∑ U : Finset (Fin n), if U.card ≤ K then term T U else 0)+
      (∑ U : Finset (Fin n), if K < U.card then term T U else 0) := by
  rw [pathCount_eq_positive_convolution, ← sum_add_distrib]
  apply sum_congr rfl
  intro U _
  by_cases h : U.card ≤ K
  · simp [h, not_lt.mpr h, term]
  · simp [h, Nat.lt_of_not_ge h, term]

lemma actual_short_lower (T : Tournament n) (K : ℕ) :
    (∑ U : Finset (Fin n), if U.card ≤ K then term T U else 0) ≤ (pathCount T : ℝ) := by
  rw [actual_short_tail_split T K]
  have hh : 0 ≤ ∑ U : Finset (Fin n), if K < U.card then term T U else 0 :=
    sum_nonneg (fun U _ => by split_ifs <;> simp_all [term_nonneg])
  linarith

lemma complement_permanent (T : Tournament n) (U : Finset (Fin n)) (m : ℕ)
    (r : Fin m ≃ {i // i ∈ Uᶜ}) :
    ((ActualReconstructionBridgeCandidate.adjacency T).submatrix
      (fun i => (r i).val) (fun i => (r i).val)).permanent =
    ((TournamentHamiltonian.adjacency T).submatrix
      (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent := by
  rw [physical_adjacency_eq]
  exact permanent_submatrix_equiv_self
    ((TournamentHamiltonian.adjacency T).submatrix
      (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val) r

/-- Finite attachment of physical bounds; the long part remains untouched.
The lower/upper inputs can be the full recoveryFactor*exp(-theta) bounds. -/
lemma physical_short_sandwich (T : Tournament n) (K : ℕ)
    (m : Finset (Fin n) → ℕ)
    (r : ∀ U : Finset (Fin n), Fin (m U) ≃ {i // i ∈ Uᶜ})
    (lo hi : Finset (Fin n) → ℝ)
    (hb : ∀ U, U.card ≤ K →
      lo U ≤ ((ActualReconstructionBridgeCandidate.adjacency T).submatrix
        (fun i => (r U i).val) (fun i => (r U i).val)).permanent ∧
      ((ActualReconstructionBridgeCandidate.adjacency T).submatrix
        (fun i => (r U i).val) (fun i => (r U i).val)).permanent ≤ hi U) :
    (∑ U : Finset (Fin n), if U.card ≤ K then (principalWeightMatrix T U).det*lo U else 0) ≤
      (∑ U : Finset (Fin n), if U.card ≤ K then term T U else 0) ∧
    (∑ U : Finset (Fin n), if U.card ≤ K then term T U else 0) ≤
      (∑ U : Finset (Fin n), if U.card ≤ K then (principalWeightMatrix T U).det*hi U else 0) := by
  constructor <;> apply sum_le_sum <;> intro U _ <;> by_cases h : U.card ≤ K
  · simp only [h, ite_true]
    have hh := (hb U h).1
    rw [complement_permanent] at hh
    exact mul_le_mul_of_nonneg_left hh (principal_weight_pos T U).le
  · simp [h]
  · simp only [h, ite_true]
    have hh := (hb U h).2
    rw [complement_permanent] at hh
    exact mul_le_mul_of_nonneg_left hh (principal_weight_pos T U).le
  · simp [h]

end ActualPathFiniteSplitCandidate
