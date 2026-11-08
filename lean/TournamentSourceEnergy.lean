import VectorWeakMajorization
import TournamentPowerComparison
import TwoBlockEnergy

/-! Actual finite directed-triangle count and source-vector energy.
The triangle count is an ordered count: each cyclic three-set contributes three.
This module does not classify extremizers or establish Assumption R. -/
namespace TournamentSourceEnergy
open Finset
open VectorWeakMajorization
noncomputable section
variable {n : ℕ} (B : Tournament n)

def cycleIndicator (i j k : Fin n) : ℝ :=
  if B.entry i j = 1 ∧ B.entry j k = 1 ∧ B.entry k i = 1 then 1 else 0

def cycleCount : ℕ :=
  (univ.filter fun t : Fin n × Fin n × Fin n =>
    B.entry t.1 t.2.1 = 1 ∧ B.entry t.2.1 t.2.2 = 1 ∧
    B.entry t.2.2 t.1 = 1).card

def energy : ℝ := ∑ i, (∑ j, B.entry i j)^2

def transitiveEnergy (n : ℕ) : ℝ := ((n : ℝ)^3-n)/3

lemma count_as_sum : ((cycleCount B) : ℝ) =
    ∑ i, ∑ j, ∑ k, (cycleIndicator B) i j k := by
  simp only [cycleCount, cycleIndicator]
  rw [← Finset.sum_boole]
  simp only [Fintype.sum_prod_type]

/-- Pointwise triangle identity, with a correction only on the full diagonal. -/
lemma local_identity (i j k : Fin n) :
    4*((cycleIndicator B) i j k+(cycleIndicator B) i k j) =
      1-(if i=j ∧ j=k then (1:ℝ) else 0) +
      B.entry i j*B.entry j k + B.entry j k*B.entry k i +
      B.entry k i*B.entry i j := by
  by_cases hij : i=j
  · subst j
    by_cases hik : i=k
    · subst k; simp [cycleIndicator, B.diagonal]
    · have hki := B.skew k i
      rcases B.unit i k hik with h|h <;>
        norm_num [cycleIndicator, B.diagonal, h, hki, hik]
  · by_cases hjk : j=k
    · subst k
      have hji := B.skew j i
      rcases B.unit i j hij with h|h <;>
        norm_num [cycleIndicator, B.diagonal, h, hji, hij]
    · by_cases hki : k=i
      · subst k
        have hji := B.skew j i
        rcases B.unit i j hij with h|h <;>
          norm_num [cycleIndicator, B.diagonal, h, hji, hij]
      · have hji := B.skew j i
        have hkj := B.skew k j
        have hik := B.skew i k
        rcases B.unit i j hij with h1|h1 <;>
          rcases B.unit j k hjk with h2|h2 <;>
          rcases B.unit k i hki with h3|h3 <;>
          norm_num [cycleIndicator, hji, hkj, hik, h1, h2, h3, hij]

lemma column_sum (j : Fin n) :
    (∑ i, B.entry i j) = -(∑ i, B.entry j i) := by
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  exact B.skew i j

lemma product_sum : (∑ i, ∑ j, ∑ k, B.entry i j*B.entry j k) = - (energy B) := by
  rw [sum_comm]
  have hrow : ∀ j, (∑ i, ∑ k, B.entry i j*B.entry j k) = -(∑ k, B.entry j k)^2 := by
    intro j
    simp only [← mul_sum, ← sum_mul]
    rw [(column_sum B)]
    ring
  simp_rw [hrow]
  simp [energy]

lemma rotate_sum (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ j, ∑ k, ∑ i, f i j k := by
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]

lemma product_sum_two : (∑ i, ∑ j, ∑ k, B.entry j k*B.entry k i) = - (energy B) := by
  rw [rotate_sum]
  exact (product_sum B)

lemma product_sum_three : (∑ i, ∑ j, ∑ k, B.entry k i*B.entry i j) = - (energy B) := by
  rw [rotate_sum, rotate_sum]
  exact (product_sum B)

/-- Ordered directed triangle count, not a hypothesis about a limiting model. -/
theorem source_energy_identity :
    3*(transitiveEnergy n - (energy B)) = 8*((cycleCount B) : ℝ) := by
  have h := congrArg (fun f : Fin n → Fin n → Fin n → ℝ =>
    ∑ i, ∑ j, ∑ k, f i j k)
    (funext fun i => funext fun j => funext fun k => (local_identity B) i j k)
  have hc : (∑ i, ∑ j, ∑ k, (cycleIndicator B) i k j) =
      ∑ i, ∑ j, ∑ k, (cycleIndicator B) i j k := by
    apply sum_congr rfl; intro i hi
    rw [sum_comm]
  simp only [sum_add_distrib, sum_sub_distrib] at h
  conv_lhs at h => simp only [← mul_sum, sum_add_distrib]
  rw [hc, ← (count_as_sum B), (product_sum B), (product_sum_two B), (product_sum_three B)] at h
  have hd : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      if i=j ∧ j=k then (1:ℝ) else 0) = n := by
    have hf : ∀ i j : Fin n, (∑ k : Fin n,
        if i=j ∧ j=k then (1:ℝ) else 0) = if j=i then 1 else 0 := by
      intro i j
      by_cases hji : j=i
      · subst j; simp
      · simp [Ne.symm hji, hji]
    simp_rw [hf]
    simp
  rw [hd] at h
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold transitiveEnergy
  nlinarith

/-- Division-free API for coupling to ordinal/two-block energy identities. -/
theorem eight_cycleCount :
    8*((cycleCount B) : ℝ) = (n : ℝ)^3-n-3*(energy B) := by
  have h := (source_energy_identity B)
  unfold transitiveEnergy at h
  nlinarith

/-- Source-vector interface used by the actual ordinal-block calculation. -/
theorem first_eq_reference_sub :
    TwoBlockEnergy.first (TournamentPowerComparison.matrix B) =
      (n : ℝ)*((n : ℝ)^2-1)/3 - 8*(((cycleCount B) : ℝ)/3) := by
  have he : TwoBlockEnergy.first (TournamentPowerComparison.matrix B) = (energy B) := by
    simp [TwoBlockEnergy.first, TournamentPowerComparison.matrix, TwoBlockEnergy.ones,
      Matrix.mulVec, dotProduct, energy]
  rw [he]
  have h := (eight_cycleCount B)
  nlinarith

end
end TournamentSourceEnergy

#print axioms TournamentSourceEnergy.eight_cycleCount
#print axioms TournamentSourceEnergy.first_eq_reference_sub
