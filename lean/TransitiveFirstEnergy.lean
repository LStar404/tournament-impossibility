import TransitiveOrbit
import TwoBlockEnergy
noncomputable section
namespace TransitiveFirstEnergy
open Finset Matrix TransitiveOrbit TwoBlockEnergy

lemma action_castSucc (n : ℕ) (i : Fin n) :
    (T (n+1)).mulVec (ones (Fin (n+1))) i.castSucc =
      (T n).mulVec (ones (Fin n)) i + 1 := by
  simp only [Matrix.mulVec, dotProduct, ones, mul_one]
  rw [Fin.sum_univ_castSucc]
  have he (j : Fin n) : T (n+1) i.castSucc j.castSucc = T n i j := rfl
  simp_rw [he]
  have hl : T (n+1) i.castSucc (Fin.last n) = 1 := by
    simp [T, Fin.lt_def, i.isLt]
  rw [hl]

lemma action_last (n : ℕ) :
    (T (n+1)).mulVec (ones (Fin (n+1))) (Fin.last n) = -(n : ℝ) := by
  simp only [Matrix.mulVec, dotProduct, ones, mul_one]
  rw [Fin.sum_univ_castSucc]
  have he (j : Fin n) : T (n+1) (Fin.last n) j.castSucc = -1 := by
    simp [T, Fin.lt_def, j.isLt, show ¬n<j.val by omega]
  simp_rw [he]
  simp [T]

lemma energy_succ (n : ℕ) :
    first (T (n+1)) = first (T n) + (n : ℝ) + (n : ℝ)^2 := by
  unfold first
  rw [Fin.sum_univ_castSucc]
  simp_rw [action_castSucc, action_last]
  have hz := TwoBlockEnergy.sum_action (T n) (T_skew n)
  rw [square_shift _ 1 hz]
  simp

/-- Exact first source energy of the actual transitive tournament, including
n=0; no spectral or recurrence identity is assumed. -/
theorem first_closed_form (n : ℕ) :
    first (T n) = (n : ℝ) * ((n : ℝ)^2 - 1) / 3 := by
  induction n with
  | zero => simp [first]
  | succ n ih =>
    rw [energy_succ, ih]
    push_cast
    ring

/-- Expanded matrix-vector form of the same formula. -/
theorem action_sum_sq (n : ℕ) :
    (∑ i : Fin n, ((T n).mulVec (fun _ => (1 : ℝ)) i)^2) =
      (n : ℝ) * ((n : ℝ)^2 - 1) / 3 :=
  first_closed_form n
end TransitiveFirstEnergy
#print axioms TransitiveFirstEnergy.first_closed_form
#print axioms TransitiveFirstEnergy.action_sum_sq
