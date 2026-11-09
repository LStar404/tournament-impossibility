import FrozenPartialPairingPolynomial
import Mathlib.RingTheory.PowerSeries.Basic

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace FrozenSeriesGrouping
open FrozenPartialPairingPolynomial SubsetPairingScaling
variable {n : ℕ} {S : Type*} [CommSemiring S]

def series (M : Matrix (Fin n) (Fin n) S) : PowerSeries S :=
  ∑ k∈Finset.range (n+1),PowerSeries.C (Fk M k)*PowerSeries.X^k

theorem weighted_group (M : Matrix (Fin n) (Fin n) S) (f : ℕ → PowerSeries S) :
    (∑ I∈Finset.univ.powerset,∑ J∈Finset.univ.powerset,
      PowerSeries.C (subsetWeight M I J)*f I.card) =
    ∑ k∈Finset.range (n+1),PowerSeries.C (Fk M k)*f k := by
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro k hk
  have hh (I : Finset (Fin n)) (hI : I∈Finset.univ.powersetCard k) :
      (∑ J∈Finset.univ.powerset,PowerSeries.C (subsetWeight M I J)*f I.card)=
      ∑ J∈Finset.univ.powersetCard k,PowerSeries.C (subsetWeight M I J)*f k := by
    have hc := (Finset.mem_powersetCard.mp hI).2
    rw [hc]
    symm
    apply Finset.sum_subset
    · intro J hJ; exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1
    · intro J hJ hnJ
      have hne : I.card ≠ J.card := by
        intro he
        exact hnJ (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,he.symm.trans hc⟩)
      rw [unequal M I J hne,map_zero,zero_mul]
  rw [Fk,map_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  rw [hh I hI,map_sum,Finset.sum_mul]

theorem degree_weight (M : Matrix (Fin n) (Fin n) S) (I J : Finset (Fin n)) :
    PowerSeries.C (subsetWeight M I J)*(PowerSeries.X : PowerSeries S)^(I.card+J.card)=
      PowerSeries.C (subsetWeight M I J)*PowerSeries.X^(2*I.card) := by
  by_cases he : I.card=J.card
  · rw [← he,two_mul]
  · rw [unequal M I J he,map_zero,zero_mul,zero_mul]

theorem series_coe (M : Matrix (Fin n) (Fin n) S) :
    series M=(frozenPolynomial M : PowerSeries S) := by
  ext k
  simp [series,frozenPolynomial,PowerSeries.coeff_C_mul_X_pow,Polynomial.coeff_sum,
    Polynomial.coeff_monomial,eq_comm]

end FrozenSeriesGrouping
#print axioms FrozenSeriesGrouping.weighted_group
