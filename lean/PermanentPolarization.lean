import PermanentAssignmentFiberCount
import Mathlib.LinearAlgebra.Matrix.Permanent
noncomputable section
namespace PermanentPositiveMoments
open MeasureTheory Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
lemma moment_as_matchings (a b : J → I) :
    (if multiplicity a=multiplicity b then ∏ i, ((multiplicity a i).factorial:ℂ) else 0) =
      ∑ s : Equiv.Perm J, if (∀ i, a (s i)=b i) then (1:ℂ) else 0 := by
  have h := matchingPerm_count a b
  have hc := congrArg (fun n : ℕ => (n:ℂ)) h
  simp only [Nat.cast_ite, Nat.cast_prod, Nat.cast_zero] at hc
  rw [← hc]
  simp [MatchingPerm, Fintype.card_subtype, Finset.sum_boole]

lemma collapse_assignment (a : J → I) (s : Equiv.Perm J) (c : (J → I) → ℂ) :
    (∑ b : J → I, c b * (if ∀i, a (s i)=b i then (1:ℂ) else 0)) =
      c (fun i => a (s i)) := by
  simp only [mul_ite, mul_one, mul_zero, ← funext_iff]
  simp

lemma permutation_assignment_sum (X Y : Matrix J I ℂ) (s : Equiv.Perm J) :
    (∑ a : J → I, assignmentWeight X a * star (assignmentWeight Y (fun i => a (s i)))) =
      ∏ i, ∑ l, X (s i) l * star (Y i l) := by
  rw [Fintype.prod_sum]
  let e : (J → I) ≃ (J → I) :=
    { toFun := fun a i => a (s.symm i)
      invFun := fun a i => a (s i)
      left_inv := fun a => by funext i; simp
      right_inv := fun a => by funext i; simp }
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [e, Equiv.coe_fn_mk, assignmentWeight, star_prod, Function.comp_apply]
  rw [← Equiv.prod_comp s (fun j => X j (a (s.symm j)))]
  simp only [s.symm_apply_apply, ← Finset.prod_mul_distrib]

 theorem polarization (X Y : Matrix J I ℂ) :
    (∫ x, density x * linearProduct X x * star (linearProduct Y x) ∂productBase) =
      Matrix.permanent (X * Yᴴ) := by
  rw [linearProduct_mixed_integral]
  simp_rw [moment_as_matchings, Finset.mul_sum]
  calc
    _ = ∑ a : J → I, ∑ s : Equiv.Perm J,
        assignmentWeight X a * star (assignmentWeight Y (fun i => a (s i))) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      exact collapse_assignment a s (fun b => assignmentWeight X a * star (assignmentWeight Y b))
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [permutation_assignment_sum]
      rfl
end PermanentPositiveMoments
#print axioms PermanentPositiveMoments.polarization
