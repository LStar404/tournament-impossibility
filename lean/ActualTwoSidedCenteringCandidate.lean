import RealProjectionAggregationCandidate
import IndependentCenteringEnergyCandidate
set_option autoImplicit false
noncomputable section
namespace ActualTwoSidedCenteringCandidate
open Matrix Finset RealGramEndpoint RealProjectionAggregationCandidate
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open IndependentCenteringEnergyCandidate
open scoped Matrix.Norms.L2Operator
variable {n m k : ℕ}
def avg (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun _ _ => (m:ℝ)⁻¹
def center (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := 1-avg m
lemma avg_symmetric (m : ℕ) : (avg m)ᵀ=avg m := rfl
lemma avg_square (hm : 0 < m) : avg m*avg m=avg m := by
  ext i j
  simp only [avg,Matrix.mul_apply,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp
lemma center_symmetric (m : ℕ) : (center m)ᵀ=center m := by
  simp only [center,Matrix.transpose_sub,Matrix.transpose_one,avg_symmetric]
lemma center_square (hm : 0 < m) : center m*center m=center m := by
  unfold center
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_sub,Matrix.mul_one,avg_square hm,sub_self,sub_zero]
lemma left_avg_energy (hm : 0 < m) (Z : Matrix (Fin m) (Fin k) ℝ) :
    frob (avg m*Z)=(∑ j,(∑ i,Z i j)^2)/(m:ℝ) := by
  have he (i : Fin m) (j : Fin k) : (avg m*Z) i j=(m:ℝ)⁻¹*∑ a,Z a j := by
    simp [Matrix.mul_apply,avg,←mul_sum]
  simp only [frob,he,mul_pow,←mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp
lemma right_avg_energy (hm : 0 < m) (Z : Matrix (Fin k) (Fin m) ℝ) :
    frob (Z*avg m)=(∑ i,(∑ j,Z i j)^2)/(m:ℝ) := by
  rw [←frob_transpose (Z*avg m),Matrix.transpose_mul,avg_symmetric,left_avg_energy hm]
  rfl
lemma centering_g_energy (hm : 0 < m) (Z : Matrix (Fin m) (Fin m) ℝ)
    (q : ℝ) (hq : 0≤q) (hq1 : q<1) (hZ : ‖Z‖≤q) :
    ‖g (center m*Z*center m)-g Z‖ ≤
      ((∑ j,(∑ i,Z i j)^2)+(∑ i,(∑ j,Z i j)^2))/(2*(m:ℝ)*(1-q^2)) := by
  have hh := two_sided_g_loss Z (center m) (center m) (center_symmetric m) (center_square hm)
    (center_symmetric m) (center_square hm) q hq hq1 hZ
  have he : 1-center m=avg m := by simp [center]
  rw [he,left_avg_energy hm,right_avg_energy hm] at hh
  convert hh using 1 <;> simp only [div_eq_mul_inv,_root_.mul_inv_rev] <;> ring
lemma enum_sum (J : Finset (Fin n)) (c : Fin m ≃ {j // j ∈ Jᶜ}) (v : Fin n → ℝ) :
    (∑ j,v (c j).val)=∑ j ∈ Jᶜ,v j := by
  rw [Equiv.sum_comp c (fun j : {j // j ∈ Jᶜ} => v j.val)]
  exact Finset.sum_coe_sort Jᶜ v
lemma retained_row_energy (T : Tournament n) (hn : 2≤n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ}) :
    (∑ i,(∑ j,realZ T (r i).val (c j).val)^2) ≤
      2*tau (normalizedScore T)+2*(n:ℝ)/((n:ℝ)-1)^2+
        2*(m:ℝ)*(J.card:ℝ)^2/((n:ℝ)-1)^2 := by
  simp_rw [enum_sum J c]
  rw [enum_sum I r (fun i => (∑ j ∈ Jᶜ,realZ T i j)^2)]
  have hc : (Iᶜ).card=m := by simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr r).symm
  simpa only [hc] using actual_restricted_row_energy T hn I J
lemma retained_col_energy (T : Tournament n) (hn : 2≤n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ}) :
    (∑ j,(∑ i,realZ T (r i).val (c j).val)^2) ≤
      2*tau (normalizedScore T)+2*(n:ℝ)/((n:ℝ)-1)^2+
        2*(m:ℝ)*(I.card:ℝ)^2/((n:ℝ)-1)^2 := by
  have he (j : Fin m) := enum_sum I r (fun i => realZ T i (c j).val)
  simp_rw [he]
  rw [enum_sum J c (fun j => (∑ i ∈ Iᶜ,realZ T i j)^2)]
  have hc : (Jᶜ).card=m := by simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr c).symm
  simpa only [hc] using actual_restricted_col_energy T hn I J
/-- Genuine Real.log(det) loss. No skew condition on the retained matrix. -/
theorem actual_centering_g_bound (T : Tournament n) (hn : 2≤n) (hm : 0 < m)
    (I J : Finset (Fin n)) (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (q : ℝ) (hq : 0≤q) (hq1 : q<1)
    (hZ : ‖(realZ T).submatrix (fun i=>(r i).val) (fun j=>(c j).val)‖≤q) :
    let Z := (realZ T).submatrix (fun i=>(r i).val) (fun j=>(c j).val)
    ‖g (center m*Z*center m)-g Z‖ ≤
      (4*tau (normalizedScore T)+4*(n:ℝ)/((n:ℝ)-1)^2+
        2*(m:ℝ)*((I.card:ℝ)^2+(J.card:ℝ)^2)/((n:ℝ)-1)^2)/(2*(m:ℝ)*(1-q^2)) := by
  dsimp only
  have hh := centering_g_energy hm _ q hq hq1 hZ
  have hr := retained_row_energy T hn I J r c
  have hc := retained_col_energy T hn I J r c
  apply hh.trans
  apply div_le_div_of_nonneg_right
  · simp only [Matrix.submatrix_apply]
    convert add_le_add hc hr using 1 <;> ring
  · have hmR : (0:ℝ) < m := by exact_mod_cast hm
    have hgap : 0≤1-q^2 := by nlinarith
    positivity
end ActualTwoSidedCenteringCandidate

#print axioms ActualTwoSidedCenteringCandidate.avg
#check ActualTwoSidedCenteringCandidate.avg

#print axioms ActualTwoSidedCenteringCandidate.center
#check ActualTwoSidedCenteringCandidate.center

#print axioms ActualTwoSidedCenteringCandidate.avg_symmetric
#check ActualTwoSidedCenteringCandidate.avg_symmetric

#print axioms ActualTwoSidedCenteringCandidate.avg_square
#check ActualTwoSidedCenteringCandidate.avg_square

#print axioms ActualTwoSidedCenteringCandidate.center_symmetric
#check ActualTwoSidedCenteringCandidate.center_symmetric

#print axioms ActualTwoSidedCenteringCandidate.center_square
#check ActualTwoSidedCenteringCandidate.center_square

#print axioms ActualTwoSidedCenteringCandidate.left_avg_energy
#check ActualTwoSidedCenteringCandidate.left_avg_energy

#print axioms ActualTwoSidedCenteringCandidate.right_avg_energy
#check ActualTwoSidedCenteringCandidate.right_avg_energy

#print axioms ActualTwoSidedCenteringCandidate.centering_g_energy
#check ActualTwoSidedCenteringCandidate.centering_g_energy

#print axioms ActualTwoSidedCenteringCandidate.enum_sum
#check ActualTwoSidedCenteringCandidate.enum_sum

#print axioms ActualTwoSidedCenteringCandidate.retained_row_energy
#check ActualTwoSidedCenteringCandidate.retained_row_energy

#print axioms ActualTwoSidedCenteringCandidate.retained_col_energy
#check ActualTwoSidedCenteringCandidate.retained_col_energy

#print axioms ActualTwoSidedCenteringCandidate.actual_centering_g_bound
#check ActualTwoSidedCenteringCandidate.actual_centering_g_bound
