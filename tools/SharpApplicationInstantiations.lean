import ActualExtremalAsymptoticCandidate
import Corollaries
import Remainder

set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false
set_option pp.deepTerms true
set_option pp.maxSteps 1000000

#check NonAlgebraicity.extremal_exponential_generating_function_nonalgebraic
  ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic
#check NonAlgebraicity.halfScale_nonalgebraic
  ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic
#check fun (q : ℕ) (hq : 2 ≤ q) => NonAlgebraicity.halfScaleRemainder_not_qRegular q hq
  ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic
#print axioms NonAlgebraicity.extremal_exponential_generating_function_nonalgebraic
#print axioms NonAlgebraicity.halfScale_nonalgebraic
#print axioms NonAlgebraicity.halfScaleRemainder_not_qRegular
#print axioms ActualExtremalAsymptoticCandidate.actual_ExtremalAsymptotic
