import FormalMixedExponential
import LinearSourceExpansion

noncomputable section
open scoped BigOperators
namespace MixedSourcePolynomials
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

def interaction (A : I → I → S) : MvPolynomial I S :=
  (-1/2:S) • ∑ i, ∑ j, A i j • (MvPolynomial.X i * MvPolynomial.X j)

theorem source_derivative (h : I → S) (i : I) :
    MvPolynomial.pderiv i (LinearSourceExpansion.source h) = MvPolynomial.C (h i) := by
  classical
  simp [LinearSourceExpansion.source, MvPolynomial.pderiv_X, Pi.single_apply, Algebra.smul_def]

theorem interaction_derivative (A : I → I → S) (hs : ∀ i j, A i j = A j i) (i : I) :
    MvPolynomial.pderiv i (interaction A) = -(∑ j, A i j • (MvPolynomial.X j : MvPolynomial I S)) := by
  classical
  have hh : MvPolynomial.pderiv i (∑ j, ∑ k, A j k • ((MvPolynomial.X j : MvPolynomial I S) * MvPolynomial.X k)) =
      (∑ j, A i j • (MvPolynomial.X j : MvPolynomial I S)) + (∑ j, A i j • (MvPolynomial.X j : MvPolynomial I S)) := by
    simp only [map_sum, Derivation.map_smul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
      smul_add, Finset.sum_add_distrib]
    simp [Pi.single_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  change MvPolynomial.pderiv i ((-1/2:S) • _) = _
  rw [Derivation.map_smul, hh, ← two_smul S, smul_smul]
  norm_num

end MixedSourcePolynomials
#print axioms MixedSourcePolynomials.interaction_derivative
