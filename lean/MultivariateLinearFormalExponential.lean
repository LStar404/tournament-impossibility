import LinearSourcePairingFactor
import ConstantPairingFormalExponential

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.typeDecidableEq
namespace MultivariateLinearFormalExponential
open OccurrenceWickPolynomial LinearSourceExpansion LinearSourcePairingFactor
open FinitePairingTransport PairingRepresentativeBridge SymmetricPairingTransport
variable {L S : Type*} [Fintype L]

/-- The quadratic contraction is h^T C h, without any positivity hypothesis. -/
theorem quadratic_eq [CommSemiring S] (C : L → L → S) (h : L → S) :
    quadratic C h = ∑ i, ∑ j, h i * C i j * h j := by
  unfold quadratic
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem wick_power [CommSemiring S] (C : L → L → S) (hs : ∀ i j, C i j = C j i)
    (h : L → S) (m : ℕ) :
    wick C hs ((source h)^m) = ConstantPairingMoments.W m (quadratic C h) := by
  classical
  letI : DecidableEq (Fin m) := Classical.typeDecidableEq _
  rw [wick_source_power]
  simp only [moment, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold ConstantPairingMoments.W moment
  apply Finset.sum_congr rfl
  intro p _
  have hf := fixed_pairing Fin.val Fin.val_injective C hs h p
  have hw : weight (fun _ _ : Fin m => quadratic C h) (fun _ _ => rfl) p =
      (quadratic C h) ^ (reps Fin.val p).card := by
    rw [weight_eq_reps Fin.val Fin.val_injective]
    simp
  apply Eq.trans _ hw.symm
  convert hf using 1
  congr 1
  ext a
  simp

def wickSeries [CommRing S] [Algebra ℚ S]
    (C : L → L → S) (hs : ∀ i j, C i j = C j i) (h : L → S) : PowerSeries S :=
  PowerSeries.mk (fun m => wick C hs ((source h)^m) *
    algebraMap ℚ S (1 / (m.factorial : ℚ)))

/-- Formal exp((h^T C h)t²/2), derived from the full repeated-index
polynomial functional. No Gaussian measure or convergence is used. -/
theorem wickSeries_eq_exp [CommRing S] [Algebra ℚ S]
    (C : L → L → S) (hs : ∀ i j, C i j = C j i) (h : L → S) :
    wickSeries C hs h = ConstantPairingFormalExponential.target (quadratic C h) := by
  rw [← ConstantPairingFormalExponential.actual_eq_exp]
  ext m
  simp only [wickSeries, ConstantPairingFormalExponential.actualSeries,
    PowerSeries.coeff_mk, wick_power]

end MultivariateLinearFormalExponential
#print axioms MultivariateLinearFormalExponential.wick_power
#print axioms MultivariateLinearFormalExponential.wickSeries_eq_exp
