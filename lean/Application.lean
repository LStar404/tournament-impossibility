import Abel
import Constant
import TournamentSequence

open Filter Topology
namespace NonAlgebraicity

/-- The precise generating function from Appendix A, including zero constant term. -/
noncomputable def extremalGeneratingFunction (z : ℂ) : ℂ :=
  ∑' n, (normalizedCoefficient n : ℂ) * z ^ n

/-- The external graph-theoretic asymptotic theorem, stated as an explicit input.
It is not asserted as an axiom or silently identified with older formalizations. -/
def ExtremalAsymptotic : Prop :=
  Tendsto (fun n => (normalizedCoefficient n : ℂ)) atTop (𝓝 extremalConstant)

theorem extremal_abel_limit (h : ExtremalAsymptotic) :
    Tendsto (fun r : ℝ => (1 - (r : ℂ)) * extremalGeneratingFunction r)
      (𝓝[<] 1) (𝓝 extremalConstant) :=
  abel_coefficient_limit _ _ h

theorem extremal_transcendental_boundary_limit
    (h : ExtremalAsymptotic) (lw : FourExponentialIndependence) :
    Tendsto (fun r : ℝ => (1 - (r : ℂ)) * extremalGeneratingFunction r)
      (𝓝[<] 1) (𝓝 extremalConstant) ∧
      Transcendental ℚ extremalConstant :=
  ⟨extremal_abel_limit h, extremalConstant_transcendental lw⟩

#print axioms extremal_transcendental_boundary_limit
end NonAlgebraicity
