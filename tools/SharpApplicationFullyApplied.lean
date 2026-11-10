import ActualExtremalAsymptoticCandidate
import Corollaries
import Remainder

set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false
set_option pp.deepTerms true

example (lw : NonAlgebraicity.FourExponentialIndependence) :
    ¬ NonAlgebraicity.HasPolynomialRelation NonAlgebraicity.exponentialFormalSeries :=
  NonAlgebraicity.extremal_exponential_generating_function_nonalgebraic
    ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic lw

example (lw : NonAlgebraicity.FourExponentialIndependence) :
    ¬ NonAlgebraicity.HasPolynomialRelation
      (PowerSeries.map (algebraMap ℚ ℂ) NonAlgebraicity.halfScaleSeries) :=
  NonAlgebraicity.halfScale_nonalgebraic
    ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic lw

example (q : ℕ) (hq : 2 ≤ q) (lw : NonAlgebraicity.FourExponentialIndependence) :
    ¬ NonAlgebraicity.IsQRegular q (fun n => (NonAlgebraicity.halfScaleRemainder n : ℂ)) :=
  NonAlgebraicity.halfScaleRemainder_not_qRegular q hq
    ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic lw

#check fun (lw : NonAlgebraicity.FourExponentialIndependence) =>
  NonAlgebraicity.extremal_exponential_generating_function_nonalgebraic
    ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic lw
#check fun (lw : NonAlgebraicity.FourExponentialIndependence) =>
  NonAlgebraicity.halfScale_nonalgebraic
    ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic lw
#check fun (q : ℕ) (hq : 2 ≤ q) (lw : NonAlgebraicity.FourExponentialIndependence) =>
  NonAlgebraicity.halfScaleRemainder_not_qRegular q hq
    ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic lw
