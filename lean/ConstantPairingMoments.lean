import PairingMomentParity

noncomputable section
open scoped BigOperators
namespace ConstantPairingMoments
open PairingDeletion SymmetricPairingTransport

def W {S : Type*} [CommSemiring S] (n : ℕ) (c : S) : S :=
  moment (fun _ _ : Fin n => c) (fun _ _ => rfl)

theorem card_rest {V : Type*} [Fintype V] [DecidableEq V] (o s : V) (hs : s ≠ o) :
    Fintype.card (Rest o s) = Fintype.card V - 2 := by
  classical
  rw [Fintype.card_of_subtype ((Finset.univ.erase o).erase s)
    (by intro x; simp [and_comm])]
  rw [Finset.card_erase_of_mem (by simp [hs]),
    Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_univ]
  omega

theorem W_zero {S : Type*} [CommSemiring S] (c : S) : W 0 c = 1 :=
  PairingMomentParity.empty_moment_one _ _

theorem W_odd {S : Type*} [CommSemiring S] (k : ℕ) (c : S) : W (2*k+1) c = 0 := by
  apply PairingMomentParity.odd_moment_zero
  rw [Fintype.card_fin]
  exact ⟨k,rfl⟩

theorem W_step {S : Type*} [CommSemiring S] (n : ℕ) (c : S) :
    W (n+2) c = (n+1 : ℕ) * c * W n c := by
  classical
  letI : DecidableEq (Fin (n+2)) := Classical.typeDecidableEq _
  unfold W
  rw [PairingMomentRecurrence.moment_recurrence _ _ (0 : Fin (n+2))]
  have he (s : {x : Fin (n+2) // x ≠ 0}) :
      moment (fun _ _ : Rest (0 : Fin (n+2)) s.val => c) (fun _ _ => rfl) =
        moment (fun _ _ : Fin n => c) (fun _ _ => rfl) := by
    let e : Rest (0 : Fin (n+2)) s.val ≃ Fin n := Fintype.equivOfCardEq (by
      rw [card_rest _ _ s.property, Fintype.card_fin, Fintype.card_fin]
      omega)
    exact moment_transport e _ _
  simp_rw [he]
  have hc : Fintype.card {x : Fin (n+2) // x ≠ 0} = n+1 := by
    rw [Fintype.card_subtype_compl (fun x : Fin (n+2) => x=0),
      Fintype.card_subtype_eq, Fintype.card_fin]
    omega
  simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
  ring

def pairFactor (k : ℕ) : ℕ := ∏ j ∈ Finset.range k, (2*j+1)

theorem pairFactor_step (k : ℕ) : pairFactor (k+1) = pairFactor k * (2*k+1) := by
  exact Finset.prod_range_succ _ _

theorem W_even {S : Type*} [CommSemiring S] (k : ℕ) (c : S) :
    W (2*k) c = (pairFactor k : S) * c^k := by
  induction k with
  | zero => simp [pairFactor,W_zero]
  | succ k ih =>
    rw [show 2*(k+1)=2*k+2 by omega,W_step,ih,pairFactor_step,pow_succ]
    push_cast
    ring

theorem factor_factorial (k : ℕ) : pairFactor k * 2^k * k.factorial = (2*k).factorial := by
  induction k with
  | zero => simp [pairFactor]
  | succ k ih =>
    rw [pairFactor_step,pow_succ,Nat.factorial_succ]
    rw [show 2*(k+1)=2*k+1+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
    calc
      _ = (2*k+2)*(2*k+1)*(pairFactor k*2^k*k.factorial) := by ring
      _ = _ := by rw [ih]; ring

end ConstantPairingMoments
#print axioms ConstantPairingMoments.W_even
#print axioms ConstantPairingMoments.factor_factorial
