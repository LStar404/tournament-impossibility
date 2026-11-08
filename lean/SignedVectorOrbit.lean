import SignedConjugacy
noncomputable section
namespace SignedVectorOrbit
open Finset Matrix SignedConjugacy
variable {n : ℕ}

def pullback (p : Equiv.Perm (Fin n)) (s x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => s (p.symm i) * x (p.symm i)

lemma related_action (p : Equiv.Perm (Fin n)) (s : Fin n → ℝ)
    (A B : Matrix (Fin n) (Fin n) ℝ) (h : Related p s A B)
    (x : Fin n → ℝ) (i : Fin n) :
    A.mulVec x i = s i * B.mulVec (pullback p s x) (p i) := by
  simp only [Matrix.mulVec, dotProduct, mul_sum]
  rw [← Equiv.sum_comp p (fun j => s i * (B (p i) j * pullback p s x j))]
  apply sum_congr rfl
  intro j hj
  rw [h i j]
  simp only [pullback, Equiv.symm_apply_apply]
  ring

lemma related_quadratic (p : Equiv.Perm (Fin n)) (s : Fin n → ℝ)
    (A B : Matrix (Fin n) (Fin n) ℝ) (h : Related p s A B)
    (x : Fin n → ℝ) :
    dotProduct x (A.mulVec x) = dotProduct (pullback p s x) (B.mulVec (pullback p s x)) := by
  unfold dotProduct
  rw [← Equiv.sum_comp p (fun i => pullback p s x i * B.mulVec (pullback p s x) i)]
  apply sum_congr rfl
  intro i hi
  rw [related_action p s A B h x i]
  simp only [pullback, Equiv.symm_apply_apply]
  ring

lemma norm_sq_gram_power (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Commute A.transpose A) (r : ℕ) (x : Fin n → ℝ) :
    (∑ i, ((A^r).mulVec x i)^2) = dotProduct x (((A.transpose*A)^r).mulVec x) := by
  calc
    _ = dotProduct ((A^r).mulVec x) ((A^r).mulVec x) := by simp only [dotProduct, pow_two]
    _ = dotProduct x ((A^r).transpose.mulVec ((A^r).mulVec x)) :=
      (Matrix.dotProduct_transpose_mulVec (A^r) x ((A^r).mulVec x)).symm
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.transpose_pow, ← h.mul_pow]

/-- Generic all-vector transport; concrete Gram assumptions must be discharged. -/
theorem norm_sq_transport (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : Commute A.transpose A) (hB : Commute B.transpose B)
    (p : Equiv.Perm (Fin n)) (s : Fin n → ℝ) (hs : ∀ i, s i*s i=1)
    (hgram : Related p s (A.transpose*A) (B.transpose*B))
    (r : ℕ) (x : Fin n → ℝ) :
    (∑ i, ((A^r).mulVec x i)^2) =
      ∑ i, ((B^r).mulVec (pullback p s x) i)^2 := by
  rw [norm_sq_gram_power A hA, norm_sq_gram_power B hB]
  exact related_quadratic p s _ _ (related_pow p s hs _ _ hgram r) x
end SignedVectorOrbit
#print axioms SignedVectorOrbit.norm_sq_transport
