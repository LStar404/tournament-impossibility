import TournamentHamiltonian.FourBlockPermanent
import ActualPathFiniteSplitCandidate
import PhysicalMinorRecoveryCandidate
set_option autoImplicit false
noncomputable section
namespace SelectedPhysicalMinorBridge
open Matrix TournamentHamiltonian ActualKappaBridgeCandidate
open ActualControlledReconstructionCandidate PhysicalMinorRecoveryCandidate
open ActualRecoveryUpperCandidate MatrixScalingMassPotential DeletedScalingSynthesisCandidate

/-- First selected set is columns, second is rows. Enumerations are independent. -/
lemma selected_eq_reindexed {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    {m : ℕ} (B : Matrix ι ι R) (rows cols : Finset ι)
    (r : Fin m ≃ rows) (c : Fin m ≃ cols) :
    selectedPermanent B cols rows =
      (B.submatrix (fun i => (r i).val) (fun j => (c j).val)).permanent := by
  exact (rectangularPermanent_submatrix_equiv
    (fun (i : rows) (j : cols) => B i j) c r).symm

/-- Deleted I are rows and deleted J are columns: selected arguments are Jᶜ,Iᶜ. -/
lemma selected_actual_eq_physical {n m : ℕ} (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ}) :
    selectedPermanent (TournamentHamiltonian.adjacency T) Jᶜ Iᶜ =
      ((ActualReconstructionBridgeCandidate.adjacency T).submatrix
        (complementEmbedding I r) (complementEmbedding J c)).permanent := by
  rw [ActualPathFiniteSplitCandidate.physical_adjacency_eq]
  exact selected_eq_reindexed (TournamentHamiltonian.adjacency T) Iᶜ Jᶜ r c

/-- Exact physical restoration for the same root. No principal-minor restriction. -/
lemma selected_same_root_recovery {n m : ℕ} (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (C ε q : ℝ) (x y : Fin m → ℝ)
    (hw : reconstructedWitness T I J r c C ε q x y) :
    selectedPermanent (TournamentHamiltonian.adjacency T) Jᶜ Iᶜ =
      recoveryFactor T I J m * Real.exp (-shiftedPotential T I J x y) *
      (expScaled (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) x y).permanent := by
  rw [selected_actual_eq_physical T I J r c]
  exact exact_same_root T I J r c C ε q x y hw
end SelectedPhysicalMinorBridge
