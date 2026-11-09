import ConstantPairingMoments

noncomputable section
open scoped BigOperators
namespace ConstantPairingCount
open ConstantPairingMoments FinitePairingTransport SymmetricPairingTransport

theorem weight_one {V : Type*} [Fintype V] (p : Pairing V) :
    SymmetricPairingTransport.weight (fun _ _ : V => (1:ℕ)) (fun _ _ => rfl) p = 1 := by
  apply Finset.prod_eq_one
  intro b hb
  induction b using Sym2.ind with
  | _ x y => rfl

theorem actual_pairing_count (k : ℕ) :
    Fintype.card (Pairing (Fin (2*k))) = pairFactor k := by
  have h := W_even k (1:ℕ)
  have hw : W (2*k) (1:ℕ) = Fintype.card (Pairing (Fin (2*k))) := by
    unfold W moment
    simp_rw [weight_one]
    simp
  rw [hw] at h
  simpa using h

end ConstantPairingCount
#print axioms ConstantPairingCount.actual_pairing_count
