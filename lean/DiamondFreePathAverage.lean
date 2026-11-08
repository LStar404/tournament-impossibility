import ActualPathConvolution
import PermanentDiagonalExpansion
import DiamondFreeDeterminant

namespace TournamentHamiltonian
open scoped Classical

/-- Integer sign matrix of exactly the same tournament, not a switched graph. -/
def asDiamondTournament {n : ℕ} (T : Tournament n) : DiamondGap.Tournament (Fin n) where
  S i j := if i = j then 0 else if T.val i j then 1 else -1
  skew i j := by
    by_cases h : i = j
    · subst j; simp
    · have ht := T.property.2 i j h
      cases hi : T.val i j <;> cases hj : T.val j i <;>
        simp_all [Ne.symm h]
  unit i j h := by simp [h]

@[simp] theorem asDiamondTournament_realMatrix {n : ℕ} (T : Tournament n) :
    DiamondFreeDeterminant.realMatrix (asDiamondTournament T) = signMatrix T := by
  ext i j
  simp only [DiamondFreeDeterminant.realMatrix, asDiamondTournament, signMatrix]
  split_ifs <;> norm_num

/-- Zero ordinary diamonds imply every even principal sign minor is one.
The hypothesis uses the already verified four-vertex diamond predicate. -/
theorem diamondFree_sign_principal_det {n : ℕ} (T : Tournament n)
    (hT : DiamondFreeRepresentation.DiamondFree (asDiamondTournament T))
    (U : Finset (Fin n)) (he : Even U.card) :
    ((signMatrix T).submatrix (Subtype.val : U → Fin n) Subtype.val).det = 1 := by
  simpa using DiamondFreeDeterminant.diamondFree_even_principal_det
    (asDiamondTournament T) hT U he

/-- Exact unnormalized two-permanent identity for an actual diamond-free
positive-order tournament. No switching invariance of the path count is used. -/
theorem diamondFree_path_two_permanents {n : ℕ} (T : Tournament (n + 1))
    (hT : DiamondFreeRepresentation.DiamondFree (asDiamondTournament T)) :
    (2 : ℝ)^n * (pathCount T : ℝ) =
      (((pathWeightMatrix T) + 1).permanent +
       ((pathWeightMatrix T) - 1).permanent) / 2 := by
  rw [actual_path_convolution_even_subsets, permanent_two_branch_average]
  apply Finset.sum_congr rfl
  intro U _
  by_cases h : Even U.card
  · simp [h, diamondFree_sign_principal_det T hT U h]
  · simp [h]

/-- Supplement S1 with its exact 1/(2n!) normalization. -/
theorem diamondFree_normalized_path_two_permanents {n : ℕ} (T : Tournament (n + 1))
    (hT : DiamondFreeRepresentation.DiamondFree (asDiamondTournament T)) :
    ((2 : ℝ)^n * (pathCount T : ℝ)) / ((n + 1).factorial : ℝ) =
      (((pathWeightMatrix T) + 1).permanent +
       ((pathWeightMatrix T) - 1).permanent) / (2 * ((n + 1).factorial : ℝ)) := by
  rw [diamondFree_path_two_permanents T hT]
  ring

end TournamentHamiltonian

namespace NonAlgebraicity
/-- The same final theorem for the original main-paper path-count function. -/
theorem diamondFree_hamiltonianPathCount_two_permanents {n : ℕ}
    (o : Orientation (n + 1))
    (h : DiamondFreeRepresentation.DiamondFree
      (TournamentHamiltonian.asDiamondTournament (asPathTournament o))) :
    ((2 : ℝ)^n * (hamiltonianPathCount o : ℝ)) / ((n + 1).factorial : ℝ) =
      (((TournamentHamiltonian.pathWeightMatrix (asPathTournament o)) + 1).permanent +
       ((TournamentHamiltonian.pathWeightMatrix (asPathTournament o)) - 1).permanent) /
      (2 * ((n + 1).factorial : ℝ)) :=
  TournamentHamiltonian.diamondFree_normalized_path_two_permanents (asPathTournament o) h
/-- Final endpoint with the literal zero unordered-diamond count hypothesis. -/
theorem zero_diamonds_hamiltonianPathCount_two_permanents {n : ℕ}
    (o : Orientation (n + 1))
    (h : (TournamentHamiltonian.asDiamondTournament (asPathTournament o)).diamonds.card = 0) :
    ((2 : ℝ)^n * (hamiltonianPathCount o : ℝ)) / ((n + 1).factorial : ℝ) =
      (((TournamentHamiltonian.pathWeightMatrix (asPathTournament o)) + 1).permanent +
       ((TournamentHamiltonian.pathWeightMatrix (asPathTournament o)) - 1).permanent) /
      (2 * ((n + 1).factorial : ℝ)) :=
  diamondFree_hamiltonianPathCount_two_permanents o
    (DiamondFreeRepresentation.diamondFree_of_card_zero _ h)
end NonAlgebraicity
