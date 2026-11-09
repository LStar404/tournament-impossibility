import ConstantPairingFormalExponential
import OccurrenceWickPolynomial

noncomputable section
namespace ScalarWickFormalExponential
open OccurrenceWickPolynomial ConstantPairingMoments ConstantPairingFormalExponential

def occurrencesEquiv (m : ℕ) : Occ (Finsupp.single () m) ≃ Fin m where
  toFun x := ⟨x.2.val,by simpa using x.2.isLt⟩
  invFun i := ⟨(),⟨i.val,by simpa using i.isLt⟩⟩
  left_inv x := by rcases x with ⟨u,k⟩; cases u; rfl
  right_inv i := rfl

theorem wick_power {S : Type*} [CommSemiring S] (c : S) (m : ℕ) :
    wick (fun _ _ : Unit => c) (fun _ _ => rfl) ((MvPolynomial.X ())^m) = W m c := by
  rw [MvPolynomial.X_pow_eq_monomial,wick_monomial,one_mul]
  exact monomialMoment_enumeration _ _ _ (occurrencesEquiv m)

/-- Exponential generating coefficients of the actual full scalar Wick
functional, not a squarefree projection. -/
def wickSeries {S : Type*} [CommRing S] [Algebra ℚ S] (c : S) : PowerSeries S :=
  PowerSeries.mk (fun m =>
    wick (fun _ _ : Unit => c) (fun _ _ => rfl) ((MvPolynomial.X ())^m) *
      algebraMap ℚ S (1/(m.factorial : ℚ)))

theorem wickSeries_eq_exp {S : Type*} [CommRing S] [Algebra ℚ S] (c : S) :
    wickSeries c = target c := by
  have h : wickSeries c = actualSeries c := by
    ext m
    simp only [wickSeries,actualSeries,PowerSeries.coeff_mk,wick_power]
  exact h.trans (actual_eq_exp c)

end ScalarWickFormalExponential
#print axioms ScalarWickFormalExponential.wick_power
#print axioms ScalarWickFormalExponential.wickSeries_eq_exp
