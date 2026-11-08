import Mathlib
noncomputable section
namespace SignedConjugacy
open Finset Matrix
variable {n : ℕ}

def Related (p : Equiv.Perm (Fin n)) (s : Fin n → ℝ)
    (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j = s i * s j * B (p i) (p j)

lemma related_one (p : Equiv.Perm (Fin n)) (s : Fin n → ℝ)
    (hs : ∀ i, s i*s i=1) : Related p s 1 1 := by
  intro i j
  by_cases hij : i=j
  · subst j; simp [Matrix.one_apply, hs]
  · have hp : p i ≠ p j := fun h => hij (p.injective h)
    simp [Matrix.one_apply, hij, hp]

lemma related_mul (p : Equiv.Perm (Fin n)) (s : Fin n → ℝ)
    (hs : ∀ i, s i*s i=1)
    (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (hAB : Related p s A B) (hCD : Related p s C D) :
    Related p s (A*C) (B*D) := by
  intro i j
  simp only [Matrix.mul_apply]
  have he : (∑ k, A i k * C k j) =
      ∑ k, s i*s j*(B (p i) (p k)*D (p k) (p j)) := by
    apply sum_congr rfl
    intro k hk
    rw [hAB, hCD]
    calc
      _ = s i*s j*(B (p i) (p k)*D (p k) (p j))*(s k*s k) := by ring
      _ = _ := by rw [hs, mul_one]
  rw [he, ← mul_sum]
  congr 1
  exact Equiv.sum_comp p (fun k => B (p i) k * D k (p j))

lemma related_pow (p : Equiv.Perm (Fin n)) (s : Fin n → ℝ)
    (hs : ∀ i, s i*s i=1) (A B : Matrix (Fin n) (Fin n) ℝ)
    (h : Related p s A B) (r : ℕ) : Related p s (A^r) (B^r) := by
  induction r with
  | zero => simpa using related_one p s hs
  | succ r ih =>
    rw [pow_succ, pow_succ]
    exact related_mul p s hs _ _ _ _ ih h

lemma column_sq_gram_power (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Commute A.transpose A) (r : ℕ) (j : Fin n) :
    (∑ i, ((A^r) i j)^2) = ((A.transpose*A)^r) j j := by
  calc
    _ = ((A^r).transpose * (A^r)) j j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
    _ = _ := by rw [Matrix.transpose_pow, ← h.mul_pow]

/-- Exact reference-column norms follow from a proved Gram conjugacy.
This is an abstract transport lemma, not a claim that a concrete K satisfies it. -/
theorem column_sq_of_gram_conjugacy (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : Commute A.transpose A) (hB : Commute B.transpose B)
    (p : Equiv.Perm (Fin n)) (s : Fin n → ℝ) (hs : ∀ i, s i*s i=1)
    (hgram : Related p s (A.transpose*A) (B.transpose*B))
    (r : ℕ) (j : Fin n) :
    (∑ i, ((A^r) i j)^2) = ∑ i, ((B^r) i (p j))^2 := by
  rw [column_sq_gram_power A hA r j, column_sq_gram_power B hB r (p j)]
  have hh := related_pow p s hs _ _ hgram r j j
  rw [hs, one_mul] at hh
  exact hh
end SignedConjugacy
#print axioms SignedConjugacy.column_sq_of_gram_conjugacy
