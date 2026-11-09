import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open scoped BigOperators
namespace BipartitePairingPermanent

/-- Partner maps on two distinct colour classes. Both inverse laws are part
of being a perfect matching, not a permanent-valued definition. -/
structure Pairing (n : ℕ) where
  left : Fin n → Fin n
  right : Fin n → Fin n
  right_left : ∀ i, right (left i) = i
  left_right : ∀ j, left (right j) = j

@[ext] theorem Pairing.ext {n : ℕ} {p q : Pairing n}
    (hl : p.left = q.left) (hr : p.right = q.right) : p = q := by
  cases p
  cases q
  simp_all

def toPerm {n : ℕ} (p : Pairing n) : Equiv.Perm (Fin n) where
  toFun := p.left
  invFun := p.right
  left_inv := p.right_left
  right_inv := p.left_right

def ofPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Pairing n where
  left := σ
  right := σ.symm
  right_left := σ.symm_apply_apply
  left_right := σ.apply_symm_apply

def pairingEquiv (n : ℕ) : Pairing n ≃ Equiv.Perm (Fin n) where
  toFun := toPerm
  invFun := ofPerm
  left_inv p := by apply Pairing.ext <;> rfl
  right_inv σ := by ext i; rfl

instance (n : ℕ) : Fintype (Pairing n) := Fintype.ofEquiv _ (pairingEquiv n).symm

/-- Actual partner permutation on all 2n vertices. -/
def partner {n : ℕ} (p : Pairing n) : Fin n ⊕ Fin n → Fin n ⊕ Fin n
  | Sum.inl i => Sum.inr (p.left i)
  | Sum.inr j => Sum.inl (p.right j)

theorem partner_involutive {n : ℕ} (p : Pairing n) : Function.Involutive (partner p) := by
  intro x
  cases x with
  | inl i => simp [partner, p.right_left]
  | inr j => simp [partner, p.left_right]

theorem partner_ne_self {n : ℕ} (p : Pairing n) (x : Fin n ⊕ Fin n) :
    partner p x ≠ x := by cases x <;> simp [partner]

/-- One factor for each edge, indexed by its unique left endpoint. -/
def weight {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n) (Fin n) R) (p : Pairing n) : R :=
  ∏ i, A i (p.left i)

def pairingSum {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n) (Fin n) R) : R := ∑ p : Pairing n, weight A p

theorem pairingSum_eq_permanent {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n) (Fin n) R) : pairingSum A = Matrix.permanent A := by
  classical
  unfold pairingSum
  calc
    ∑ p : Pairing n, weight A p = ∑ σ : Equiv.Perm (Fin n), ∏ i, A i (σ i) :=
      Fintype.sum_equiv (pairingEquiv n) _ _ (fun p => rfl)
    _ = Matrix.permanent A.transpose := by rfl
    _ = Matrix.permanent A := Matrix.permanent_transpose A

end BipartitePairingPermanent
#print axioms BipartitePairingPermanent.pairingSum_eq_permanent
