import PermanentFiniteMixedIntegral
import Mathlib.Algebra.BigOperators.Ring.Finset
noncomputable section
namespace PermanentPositiveMoments
open MeasureTheory
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def multiplicity (a : J → I) (i : I) : ℕ := (Finset.univ.filter (fun j => a j=i)).card

def density (x : I → RadialPhase) : ℂ := ∏ i, (Real.exp (-(x i).1):ℂ)
def linearProduct (X : Matrix J I ℂ) (x : I → RadialPhase) : ℂ :=
  ∏ j, ∑ i, X j i * coordinate (x i)
def assignmentWeight (X : Matrix J I ℂ) (a : J → I) : ℂ := ∏ j, X j (a j)

lemma product_coordinates (a : J → I) (g : I → ℂ) :
    (∏ j, g (a j)) = ∏ i, g i ^ multiplicity a i := by
  simpa [multiplicity] using (Finset.prod_fiberwise' Finset.univ a g).symm

lemma linearProduct_expansion (X : Matrix J I ℂ) (x : I → RadialPhase) :
    linearProduct X x = ∑ a : J → I, assignmentWeight X a *
      ∏ i, coordinate (x i)^multiplicity a i := by
  unfold linearProduct
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.prod_mul_distrib, product_coordinates a (fun i => coordinate (x i))]
  rfl

lemma density_monomial (a b : I → ℕ) (x : I → RadialPhase) :
    density x * (∏ i, coordinate (x i)^a i) * star (∏ i, coordinate (x i)^b i) =
      mixedMonomial a b x := by
  simp only [density, mixedMonomial, mixedIntegrand, star_prod,
    ← Finset.prod_mul_distrib]

lemma linearProduct_mixed_expansion (X Y : Matrix J I ℂ) (x : I → RadialPhase) :
    density x * linearProduct X x * star (linearProduct Y x) =
      ∑ a : J → I, ∑ b : J → I,
        (assignmentWeight X a * star (assignmentWeight Y b)) *
          mixedMonomial (multiplicity a) (multiplicity b) x := by
  rw [linearProduct_expansion, linearProduct_expansion]
  simp only [star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← density_monomial]
  ring

theorem linearProduct_mixed_integral (X Y : Matrix J I ℂ) :
    (∫ x, density x * linearProduct X x * star (linearProduct Y x) ∂productBase) =
      ∑ a : J → I, ∑ b : J → I,
        (assignmentWeight X a * star (assignmentWeight Y b)) *
        (if multiplicity a=multiplicity b then ∏ i, ((multiplicity a i).factorial:ℂ) else 0) := by
  simp_rw [linearProduct_mixed_expansion]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    exact finite_mixed_integral Finset.univ
      (fun b => assignmentWeight X a * star (assignmentWeight Y b))
      (fun _ => multiplicity a) multiplicity
  · intro a ha
    exact integrable_finset_sum _ (fun b hb =>
      (mixedMonomial_integrable (multiplicity a) (multiplicity b)).const_mul _)
end PermanentPositiveMoments
#print axioms PermanentPositiveMoments.linearProduct_mixed_integral
