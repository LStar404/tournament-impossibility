import PairingEndpointEquiv
import LinearSourceExpansion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace LinearSourcePairingFactor
open FinitePairingTransport PairingRepresentativeBridge SymmetricPairingTransport
variable {V L S : Type*} [Fintype V] [Fintype L] [CommSemiring S]

def quadratic (C : L → L → S) (h : L → S) : S := ∑ i, ∑ j, h i * h j * C i j

def assignmentEquiv (rank : V → ℕ) (hi : Function.Injective rank) (p : Pairing V) :
    (V → L) ≃ ((reps rank p) → Bool → L) :=
  (Equiv.arrowCongr (PairingEndpointEquiv.equivalence rank hi p).symm (Equiv.refl L)).trans
    (Equiv.curry _ _ _)

theorem assignment_false (rank : V → ℕ) (hi : Function.Injective rank) (p : Pairing V)
    (a : V → L) (r : reps rank p) : assignmentEquiv rank hi p a r false = a r := rfl

theorem assignment_true (rank : V → ℕ) (hi : Function.Injective rank) (p : Pairing V)
    (a : V → L) (r : reps rank p) : assignmentEquiv rank hi p a r true = a (p.val r) := rfl

theorem vertex_product (rank : V → ℕ) (hi : Function.Injective rank) (p : Pairing V)
    (a : V → L) (h : L → S) :
    (∏ x, h (a x)) = ∏ r : reps rank p, h (a r) * h (a (p.val r)) := by
  rw [← (PairingEndpointEquiv.equivalence rank hi p).prod_comp (fun x => h (a x)),
    Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro r _
  rw [Fintype.prod_bool]
  change h (a (p.val r)) * h (a r) = _
  exact mul_comm _ _

theorem edge_sum (C : L → L → S) (h : L → S) :
    (∑ b : Bool → L, h (b false) * h (b true) * C (b false) (b true)) = quadratic C h := by
  classical
  rw [← (Equiv.boolArrowEquivProd L).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Equiv.boolArrowEquivProd, Equiv.coe_fn_symm_mk]
  simp [quadratic]

theorem fixed_pairing (rank : V → ℕ) (hi : Function.Injective rank)
    (C : L → L → S) (hs : ∀ i j, C i j = C j i) (h : L → S) (p : Pairing V) :
    (∑ a : V → L, (∏ x, h (a x)) *
      weight (fun x y => C (a x) (a y)) (fun x y => hs _ _) p) =
      (quadratic C h) ^ (reps rank p).card := by
  classical
  calc
    _ = ∑ b : (reps rank p) → Bool → L,
        ∏ r, h (b r false) * h (b r true) * C (b r false) (b r true) := by
      apply Fintype.sum_equiv (assignmentEquiv rank hi p)
      intro a
      rw [vertex_product rank hi p, weight_eq_reps rank hi]
      rw [← Finset.prod_coe_sort (reps rank p) (fun x => C (a x) (a (p.val x))),
        ← Finset.prod_mul_distrib]
      rfl
    _ = ∏ r : reps rank p, ∑ b : Bool → L,
        h (b false) * h (b true) * C (b false) (b true) := by
      rw [Fintype.prod_sum]
    _ = _ := by simp [edge_sum]

end LinearSourcePairingFactor
#print axioms LinearSourcePairingFactor.fixed_pairing
