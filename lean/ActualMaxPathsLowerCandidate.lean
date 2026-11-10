import ActualUnitPathLowerCandidate
import CarouselPathLowerFocused
set_option autoImplicit false
namespace ActualMaxPathsLowerCandidate
open TournamentHamiltonian
/-- No external minor, generating-det or path lower hypothesis remains. -/
theorem actual_maxPaths_lower_uniform :
    ∃ C : ℝ,0≤C ∧ ∃ N : ℕ,2≤N ∧ ∀ n : ℕ,N≤n →
      (lowerConstant-C/(n:ℝ))*meanPaths n ≤ (maxPaths n:ℝ) :=
  maxPaths_lower_uniform_of_unit_score ActualUnitPathLowerCandidate.actual_unit_path_lower_uniform
end ActualMaxPathsLowerCandidate
