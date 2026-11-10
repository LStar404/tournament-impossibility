import IndependentDeletionLossCandidate
import TournamentPrescalingMassBound
set_option autoImplicit false
noncomputable section
namespace IndependentCenteringEnergyCandidate
open Matrix Finset TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
variable {n : ℕ}
def realZ (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (signMatrix T i j-(if i=j then 1 else 0))/((n:ℝ)-1)
lemma realZ_row (T : Tournament n) (i : Fin n) :
    (∑ j,realZ T i j)=normalizedScore T i-1/((n:ℝ)-1) := by
  simp [realZ,←sum_div,sum_sub_distrib,score,normalizedScore,sub_div]
lemma realZ_col (T : Tournament n) (j : Fin n) :
    (∑ i,realZ T i j)= -normalizedScore T j-1/((n:ℝ)-1) := by
  simp only [realZ,←sum_div,sum_sub_distrib]
  simp_rw [signMatrix_skew T _ j]
  simp [score,normalizedScore,sub_div,neg_div]
lemma shifted_energy (a : Fin n → ℝ) (ha : ∑ i,a i=0) (d : ℝ) :
    (∑ i,(a i-d)^2)=tau a+(n:ℝ)*d^2 := by
  simp_rw [sub_sq]
  simp [sum_add_distrib,sum_sub_distrib,←sum_mul,←mul_sum,ha,tau]
lemma full_row_energy (T : Tournament n) :
    (∑ i,(∑ j,realZ T i j)^2)=tau (normalizedScore T)+(n:ℝ)/((n:ℝ)-1)^2 := by
  simp_rw [realZ_row]
  rw [shifted_energy _ (ActualTournamentPrescalingBounds.score_sum_zero T)]
  simp only [div_pow,one_pow]
  ring
lemma full_col_energy (T : Tournament n) :
    (∑ j,(∑ i,realZ T i j)^2)=tau (normalizedScore T)+(n:ℝ)/((n:ℝ)-1)^2 := by
  simp_rw [realZ_col]
  have hz : ∑ j,-normalizedScore T j=0 := by simp [ActualTournamentPrescalingBounds.score_sum_zero]
  rw [shifted_energy _ hz]
  simp only [tau,neg_sq]
  simp only [div_pow,one_pow]
  ring
lemma realZ_abs (T : Tournament n) (hn : 2≤n) (i j : Fin n) :
    |realZ T i j|≤1/((n:ℝ)-1) := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hh := signMatrix_sq T i j
  have hn0 : 0≤(n:ℝ)-1 := by linarith
  rw [realZ,abs_div,abs_of_nonneg hn0]
  apply div_le_div_of_nonneg_right _ hn0
  by_cases hij : i=j
  · subst j
    simp [signMatrix]
  · simp only [if_neg hij,sub_zero]
    simp only [if_neg hij] at hh
    exact (abs_le.mpr ⟨by nlinarith,by nlinarith⟩)

lemma restricted_energy_bound (Z : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) {d : ℝ} (hd : 0≤d) (hZ : ∀ i j,|Z i j|≤d) :
    (∑ i ∈ Iᶜ,(∑ j ∈ Jᶜ,Z i j)^2) ≤
      2*(∑ i,(∑ j,Z i j)^2)+2*((Iᶜ).card:ℝ)*(J.card:ℝ)^2*d^2 := by
  have hremoved (i : Fin n) : |∑ j ∈ J,Z i j|≤(J.card:ℝ)*d := by
    calc
      _ ≤ ∑ j ∈ J,|Z i j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ J,d := sum_le_sum (fun j _=>hZ i j)
      _ = _ := by simp
  have hpoint (i : Fin n) : (∑ j ∈ Jᶜ,Z i j)^2 ≤
      2*(∑ j,Z i j)^2+2*(J.card:ℝ)^2*d^2 := by
    have hsplit := sum_add_sum_compl J (fun j=>Z i j)
    have hsq := mul_self_le_mul_self (abs_nonneg (∑ j ∈ J,Z i j)) (hremoved i)
    simp only [←pow_two,sq_abs,mul_pow] at hsq
    have heq : (∑ j ∈ Jᶜ,Z i j)=(∑ j,Z i j)-(∑ j ∈ J,Z i j) := by linarith
    rw [heq]
    nlinarith [sq_nonneg ((∑ j,Z i j)+(∑ j ∈ J,Z i j))]
  have hsub : (∑ i ∈ Iᶜ,(∑ j,Z i j)^2)≤∑ i,(∑ j,Z i j)^2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>sq_nonneg _)
  calc
    _ ≤ ∑ i ∈ Iᶜ,(2*(∑ j,Z i j)^2+2*(J.card:ℝ)^2*d^2) := sum_le_sum (fun i _=>hpoint i)
    _ = 2*(∑ i ∈ Iᶜ,(∑ j,Z i j)^2)+2*((Iᶜ).card:ℝ)*(J.card:ℝ)^2*d^2 := by
      simp [sum_add_distrib,←mul_sum]
      ring
    _ ≤ _ := by linarith
lemma actual_restricted_row_energy (T : Tournament n) (hn : 2≤n) (I J : Finset (Fin n)) :
    (∑ i ∈ Iᶜ,(∑ j ∈ Jᶜ,realZ T i j)^2) ≤
      2*tau (normalizedScore T)+2*(n:ℝ)/((n:ℝ)-1)^2+
        2*((Iᶜ).card:ℝ)*(J.card:ℝ)^2/((n:ℝ)-1)^2 := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hh := restricted_energy_bound (realZ T) I J
    (show 0≤1/((n:ℝ)-1) by apply div_nonneg (by norm_num); linarith) (realZ_abs T hn)
  rw [full_row_energy] at hh
  simp only [div_pow,one_pow] at hh
  convert hh using 1 <;> ring
lemma actual_restricted_col_energy (T : Tournament n) (hn : 2≤n) (I J : Finset (Fin n)) :
    (∑ j ∈ Jᶜ,(∑ i ∈ Iᶜ,realZ T i j)^2) ≤
      2*tau (normalizedScore T)+2*(n:ℝ)/((n:ℝ)-1)^2+
        2*((Jᶜ).card:ℝ)*(I.card:ℝ)^2/((n:ℝ)-1)^2 := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hh := restricted_energy_bound (realZ T).transpose J I
    (show 0≤1/((n:ℝ)-1) by apply div_nonneg (by norm_num); linarith) (fun i j=>realZ_abs T hn j i)
  simp only [Matrix.transpose_apply] at hh
  rw [full_col_energy] at hh
  simp only [div_pow,one_pow] at hh
  convert hh using 1 <;> ring
end IndependentCenteringEnergyCandidate

#print axioms IndependentCenteringEnergyCandidate.realZ
#check IndependentCenteringEnergyCandidate.realZ

#print axioms IndependentCenteringEnergyCandidate.realZ_row
#check IndependentCenteringEnergyCandidate.realZ_row

#print axioms IndependentCenteringEnergyCandidate.realZ_col
#check IndependentCenteringEnergyCandidate.realZ_col

#print axioms IndependentCenteringEnergyCandidate.shifted_energy
#check IndependentCenteringEnergyCandidate.shifted_energy

#print axioms IndependentCenteringEnergyCandidate.full_row_energy
#check IndependentCenteringEnergyCandidate.full_row_energy

#print axioms IndependentCenteringEnergyCandidate.full_col_energy
#check IndependentCenteringEnergyCandidate.full_col_energy

#print axioms IndependentCenteringEnergyCandidate.realZ_abs
#check IndependentCenteringEnergyCandidate.realZ_abs

#print axioms IndependentCenteringEnergyCandidate.restricted_energy_bound
#check IndependentCenteringEnergyCandidate.restricted_energy_bound

#print axioms IndependentCenteringEnergyCandidate.actual_restricted_row_energy
#check IndependentCenteringEnergyCandidate.actual_restricted_row_energy

#print axioms IndependentCenteringEnergyCandidate.actual_restricted_col_energy
#check IndependentCenteringEnergyCandidate.actual_restricted_col_energy
