import SubsetPairingScaling
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Polynomial.Eval.Defs

noncomputable section
open scoped BigOperators
namespace FrozenPartialPairingPolynomial
open SubsetPairingScaling

def globalWeight {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) : S :=
  ∑ I ∈ Finset.univ.powerset, ∑ J ∈ Finset.univ.powerset, subsetWeight M I J

/-- M is fixed, independent of the later generating variable. -/
def Fk {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (k : ℕ) : S :=
  ∑ I ∈ Finset.univ.powersetCard k, ∑ J ∈ Finset.univ.powersetCard k, subsetWeight M I J

theorem inner_restrict {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (I : Finset (Fin n)) :
    (∑ J ∈ Finset.univ.powerset, subsetWeight M I J) =
      ∑ J ∈ Finset.univ.powersetCard I.card, subsetWeight M I J := by
  symm
  apply Finset.sum_subset
  · intro J hJ
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1
  · intro J hJ hnJ
    apply unequal
    intro hc
    apply hnJ
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc.symm⟩

theorem grouped {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) :
    globalWeight M = ∑ k ∈ Finset.range (n+1), Fk M k := by
  unfold globalWeight
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro k hk
  unfold Fk
  apply Finset.sum_congr rfl
  intro I hI
  rw [inner_restrict, (Finset.mem_powersetCard.mp hI).2]

theorem Fk_smul {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (z : S) (k : ℕ) :
    Fk (z • M) k = z^k * Fk M k := by
  unfold Fk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [smul, (Finset.mem_powersetCard.mp hI).2]

theorem global_smul {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (z : S) :
    globalWeight (z • M) = ∑ k ∈ Finset.range (n+1), Fk M k * z^k := by
  rw [grouped]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Fk_smul, mul_comm]

def frozenPolynomial {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) : Polynomial S :=
  ∑ k ∈ Finset.range (n+1), Polynomial.monomial k (Fk M k)

theorem eval_frozenPolynomial {n : ℕ} {S : Type*} [CommSemiring S]
    (M : Matrix (Fin n) (Fin n) S) (z : S) :
    (frozenPolynomial M).eval z = globalWeight (z • M) := by
  rw [global_smul]
  simp [frozenPolynomial, Polynomial.eval_finsetSum]

end FrozenPartialPairingPolynomial
#print axioms FrozenPartialPairingPolynomial.global_smul
#print axioms FrozenPartialPairingPolynomial.eval_frozenPolynomial
