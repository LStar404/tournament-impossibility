import Mathlib

noncomputable section
namespace RawBlockSourceIdentity
open Matrix

def ones (n : ℕ) : Fin n ⊕ Fin n → ℂ := fun _ => 1

def rawSource {n : ℕ} (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) : ℂ :=
  (ones n ⬝ᵥ (((B-1)*B⁻¹).mulVec (ones n)))/2

def sumSolution {n : ℕ} (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) : Fin n → ℂ :=
  fun i => (B⁻¹.mulVec (ones n)) (Sum.inl i)+(B⁻¹.mulVec (ones n)) (Sum.inr i)

/-- The source starts from the genuine block inverse and its 2n-dimensional
bilinear quadratic form. It is not defined to be the reduced scalar answer. -/
theorem source_eq_reduced {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (hB : B*B⁻¹=1) :
    rawSource B=(n:ℂ)-((fun _ : Fin n => (1:ℂ)) ⬝ᵥ sumSolution B)/2 := by
  have hW : (B-1)*B⁻¹=1-B⁻¹ := by rw [sub_mul,hB,one_mul]
  have hsum : ones n ⬝ᵥ (B⁻¹.mulVec (ones n))=
      (fun _ : Fin n => (1:ℂ)) ⬝ᵥ sumSolution B := by
    simp [ones,sumSolution,dotProduct,Fintype.sum_sum_type,Finset.sum_add_distrib]
  have hones : ones n ⬝ᵥ ones n=2*(n:ℂ) := by simp [ones,dotProduct]; ring
  unfold rawSource
  rw [hW,Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub,hones,hsum]
  ring
end RawBlockSourceIdentity
#print axioms RawBlockSourceIdentity.source_eq_reduced
