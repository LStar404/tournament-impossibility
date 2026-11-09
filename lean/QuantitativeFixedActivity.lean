import ActualDegreeAssignmentCount
import ActivityNumericalBound
import ActualFiniteActivity
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace QuantitativeFixedActivity
open WeightedCoefficientNorm StructuralPartialMatchingCounts PhysicalTiltedCovariance
variable {I : Type*} [Fintype I]

def singleConstant (M : ℝ) := (2:ℝ)^8*6^3*Real.exp 1*M^3
def totalConstant (M : ℝ) := (2:ℝ)^15*6^3*Real.exp 1*M^3

theorem labeled_uniform {b n : ℕ} (hn : 0<n) (hc : Fintype.card I=2*n)
    (K A : I → I → ℂ) (hK : ∀i j,K i j=K j i) (hA : ∀i j,A i j=A j i)
    (h : I → ℂ) (d : Fin b →₀ ℕ) (hd : ∀v,3 ≤ d v) (j : ℕ) (hj : 1 ≤ j)
    (rho M : ℝ) (hr : 0 ≤ rho) (hM : 1 ≤ M)
    (hW : ∀i j,Finite rho (covariance K A i j)) (heta : ∀i,Finite rho (mean K A h i))
    (bW : ∀i j,norm rho (covariance K A i j) ≤ M/(n:ℝ))
    (beta : ∀i,norm rho (mean K A h i) ≤ M/(n:ℝ)) :
    Finite rho (StructuralActivityWeighted.labeled K A hK hA h d j) ∧
    norm rho (StructuralActivityWeighted.labeled K A hK hA h d j) ≤
      (singleConstant M*(j:ℝ)/(n:ℝ))^j := by
  by_cases hp : Nonempty (StructuralActivityCount.Fiber d j)
  · obtain ⟨p,hp⟩ := hp
    let D := ∑v,d v
    let e := pairCount p
    let s := singletonCount p
    have ht : D=2*e+s := total_degree d p
    have hstruct := structural_bounds d hd p
    have hes : e+s=j+b := by simpa only [hp] using hstruct.2.2
    have hb : b ≤ 2*j := by simpa only [hp] using hstruct.1
    have hD : D ≤ 6*j := by simpa only [hp] using hstruct.2.1
    have he : e ≤ 3*j := by omega
    have hpos : 0 ≤ M/(n:ℝ) := by positivity
    have hl := StructuralActivityWeighted.labeled_bound K A hK hA h d hd D e s j rfl ht hes
      rho (M/n) (M/n) hr hpos hpos hW heta bW beta
    constructor
    · exact hl.1
    · apply hl.2.trans
      rw [hc]
      push_cast
      exact ActivityNumericalBound.scaled n j b D e s hn hj hb hD he hes M hM
  · have hz : StructuralActivityWeighted.labeled K A hK hA h d j=0 := by
      unfold StructuralActivityWeighted.labeled StructuralActivitySeries.word
      have hnz (p : PartialMatchingAffine.PartialPairing (Positions d)) : ¬activityIndex d p=j :=
        fun heq => hp ⟨⟨p,heq⟩⟩
      simp [hnz]
    rw [hz]
    exact ⟨WeightedCoefficientSums.finite_zero rho,by rw [WeightedCoefficientSums.norm_zero]; dsimp [singleConstant]; positivity⟩
theorem degree_uniform {n : ℕ} (hn : 0<n) (hc : Fintype.card I=2*n)
    (K A : I → I → ℂ) (hK : ∀i j,K i j=K j i) (hA : ∀i j,A i j=A j i)
    (h : I → ℂ) (D j : ℕ) (hj : 1 ≤ j)
    (rho M : ℝ) (hr : 0 ≤ rho) (hM : 1 ≤ M)
    (hW : ∀i j,Finite rho (covariance K A i j)) (heta : ∀i,Finite rho (mean K A h i))
    (bW : ∀i j,norm rho (covariance K A i j) ≤ M/(n:ℝ))
    (beta : ∀i,norm rho (mean K A h i) ≤ M/(n:ℝ)) :
    Finite rho (StructuralActivitySeries.degree K A hK hA h D j) ∧
    norm rho (StructuralActivitySeries.degree K A hK hA h D j) ≤
      (2:ℝ)^(D-1)*(singleConstant M*(j:ℝ)/(n:ℝ))^j := by
  rw [ActualDegreeAssignmentCount.degree_eq]
  have hb (p : Σb : ℕ,Fin b →₀ ℕ) (hp : p∈ActualDegreeAssignmentCount.allAssignments D) :=
    labeled_uniform hn hc K A hK hA h p.2
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2 j hj rho M hr hM hW heta bW beta
  constructor
  · exact WeightedCoefficientSums.sum_finite _ _ hr (fun p hp => (hb p hp).1)
  · apply (WeightedCoefficientSums.sum_norm _ _ hr (fun p hp => (hb p hp).1)).trans
    calc
      _ ≤ ∑p∈ActualDegreeAssignmentCount.allAssignments D,(singleConstant M*(j:ℝ)/(n:ℝ))^j :=
        Finset.sum_le_sum (fun p hp => (hb p hp).2)
      _ = ((ActualDegreeAssignmentCount.allAssignments D).card:ℝ)*(singleConstant M*(j:ℝ)/(n:ℝ))^j := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast ActualDegreeAssignmentCount.count D) (by dsimp [singleConstant]; positivity)

theorem sum_two (N : ℕ) : (∑D∈Finset.range N,(2:ℝ)^D) ≤ 2^N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,pow_succ]; linarith

/-- Quantitative bound for the actual finite activity series. This does not assert an
infinite-j series is summable at fixed n, nor a permanent-circle envelope. -/
theorem bound {n : ℕ} (hn : 0<n) (hc : Fintype.card I=2*n)
    (K A : I → I → ℂ) (hK : ∀i j,K i j=K j i) (hA : ∀i j,A i j=A j i)
    (h : I → ℂ) (j : ℕ) (hj : 1 ≤ j)
    (rho M : ℝ) (hr : 0 ≤ rho) (hM : 1 ≤ M)
    (hW : ∀i j,Finite rho (covariance K A i j)) (heta : ∀i,Finite rho (mean K A h i))
    (bW : ∀i j,norm rho (covariance K A i j) ≤ M/(n:ℝ))
    (beta : ∀i,norm rho (mean K A h i) ≤ M/(n:ℝ)) :
    Finite rho (ActualFiniteActivity.series K A hK hA h j) ∧
    norm rho (ActualFiniteActivity.series K A hK hA h j) ≤
      (totalConstant M*(j:ℝ)/(n:ℝ))^j := by
  have hd (D : ℕ) := degree_uniform hn hc K A hK hA h D j hj rho M hr hM hW heta bW beta
  unfold ActualFiniteActivity.series
  constructor
  · exact WeightedCoefficientSums.sum_finite _ _ hr (fun D _ => (hd D).1)
  · apply (WeightedCoefficientSums.sum_norm _ _ hr (fun D _ => (hd D).1)).trans
    let T := (singleConstant M*(j:ℝ)/(n:ℝ))^j
    have hT : 0 ≤ T := by dsimp [T,singleConstant]; positivity
    calc
      _ ≤ ∑D∈Finset.range (6*j+1),(2:ℝ)^(D-1)*T := Finset.sum_le_sum (fun D _ => (hd D).2)
      _ ≤ ∑D∈Finset.range (6*j+1),(2:ℝ)^D*T := Finset.sum_le_sum (fun D _ =>
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hT)
      _ = (∑D∈Finset.range (6*j+1),(2:ℝ)^D)*T := by rw [Finset.sum_mul]
      _ ≤ (2:ℝ)^(6*j+1)*T := mul_le_mul_of_nonneg_right (sum_two _) hT
      _ ≤ (2:ℝ)^(7*j)*T := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hT
      _ = _ := by
        dsimp [T,singleConstant,totalConstant]
        rw [pow_mul,← mul_pow]
        congr 1
        ring
end QuantitativeFixedActivity
#print axioms QuantitativeFixedActivity.bound
#print axioms QuantitativeFixedActivity.labeled_uniform
