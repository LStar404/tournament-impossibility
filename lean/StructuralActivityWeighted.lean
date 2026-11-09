import StructuralActivitySeries
import StructuralActivityCount
import WeightedCoefficientSums
import PartialMatchingWeightedBound
import ActivityFactorialSuppression
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace StructuralActivityWeighted
open StructuralPartialMatchingCounts PartialMatchingAffine WeightedCoefficientNorm PhysicalTiltedCovariance
variable {I : Type*} [Fintype I]

theorem word_bound {b : ℕ} (K A : I → I → ℂ) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → ℂ) (d : Fin b →₀ ℕ) (hd : ∀v,3 ≤ d v)
    (a : Fin b → I) (D e s j : ℕ) (hD : (∑v,d v)=D) (hde : D=2*e+s) (hj : e+s=j+b)
    (rho U V : ℝ) (hr : 0 ≤ rho) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hW : ∀i j,Finite rho (covariance K A i j)) (heta : ∀i,Finite rho (mean K A h i))
    (bW : ∀i j,norm rho (covariance K A i j) ≤ U) (beta : ∀i,norm rho (mean K A h i) ≤ V) :
    Finite rho (StructuralActivitySeries.word K A hK hA h d a j) ∧
    norm rho (StructuralActivitySeries.word K A hK hA h d a j) ≤
      (2:ℝ)^D*(D:ℝ)^e*U^e*V^s := by
  let w (p : PartialPairing (Positions d)) := weight (covariance K A)
    (PhysicalPartialMatching.covariance_symmetry K A hK hA) (mean K A h)
    (fun x : Positions d => a x.1) p
  have hw (p : PartialPairing (Positions d)) := PartialMatchingWeightedBound.bound
    (covariance K A) (PhysicalPartialMatching.covariance_symmetry K A hK hA)
    (mean K A h) (fun x : Positions d => a x.1) p hr hU hV hW heta bW beta
  have hf (p : PartialPairing (Positions d)) : Finite rho (if activityIndex d p=j then w p else 0) := by
    split_ifs
    · exact (hw p).1
    · exact WeightedCoefficientSums.finite_zero rho
  change Finite rho (∑p,if activityIndex d p=j then w p else 0) ∧ _
  constructor
  · exact WeightedCoefficientSums.sum_finite _ _ hr (fun p _ => hf p)
  · apply (WeightedCoefficientSums.sum_norm Finset.univ _ hr (fun p _ => hf p)).trans
    have hc : ((Finset.univ : Finset (PartialPairing (Positions d))).filter
        (fun p => activityIndex d p=j)).card=Fintype.card (StructuralActivityCount.Fiber d j) := by
      symm
      exact Fintype.card_of_subtype _ (by intro p; simp)
    have hn : (Fintype.card (StructuralActivityCount.Fiber d j):ℝ) ≤ (2:ℝ)^D*(D:ℝ)^e := by
      exact_mod_cast StructuralActivityCount.bound d hd D e s j hD hde hj
    calc
      _ ≤ ∑p:PartialPairing (Positions d),if activityIndex d p=j then U^e*V^s else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        split_ifs with hpj
        · have heq := (StructuralActivityCount.counts d hd D e s j hD hde hj p).mp hpj
          have hsq : singletonCount p=s := by have ht := total_degree d p; omega
          simpa only [heq,hsq] using (hw p).2
        · simp [WeightedCoefficientSums.norm_zero]
      _ = (Fintype.card (StructuralActivityCount.Fiber d j):ℝ)*(U^e*V^s) := by
        rw [← Finset.sum_filter]
        simp [hc]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hn (mul_nonneg (pow_nonneg hU e) (pow_nonneg hV s))
        simpa only [mul_assoc] using hh
/-- Actual labeled scalar contribution, retaining 1/b! rather than dropping it. -/
def labeled {b : ℕ} (K A : I → I → ℂ) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → ℂ) (d : Fin b →₀ ℕ) (j : ℕ) : PowerSeries ℂ :=
  ∑a : Fin b → I,PowerSeries.C (OrderedResidualPolynomial.scalar (S:=ℂ) d)*
    StructuralActivitySeries.word K A hK hA h d a j

theorem labeled_bound {b : ℕ} (K A : I → I → ℂ) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → ℂ) (d : Fin b →₀ ℕ) (hd : ∀v,3 ≤ d v)
    (D e s j : ℕ) (hD : (∑v,d v)=D) (hde : D=2*e+s) (hj : e+s=j+b)
    (rho U V : ℝ) (hr : 0 ≤ rho) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hW : ∀i j,Finite rho (covariance K A i j)) (heta : ∀i,Finite rho (mean K A h i))
    (bW : ∀i j,norm rho (covariance K A i j) ≤ U) (beta : ∀i,norm rho (mean K A h i) ≤ V) :
    Finite rho (labeled K A hK hA h d j) ∧
    norm rho (labeled K A hK hA h d j) ≤
      (1/(b.factorial:ℝ))*(Fintype.card I:ℝ)^b*((2:ℝ)^D*(D:ℝ)^e*U^e*V^s) := by
  have hw (a : Fin b → I) := word_bound K A hK hA h d hd a D e s j hD hde hj
    rho U V hr hU hV hW heta bW beta
  have hf (a : Fin b → I) := WeightedCoefficientSums.scalar_finite rho
    (OrderedResidualPolynomial.scalar (S:=ℂ) d) _ (hw a).1
  unfold labeled
  constructor
  · exact WeightedCoefficientSums.sum_finite _ _ hr (fun a _ => hf a)
  · apply (WeightedCoefficientSums.sum_norm Finset.univ _ hr (fun a _ => hf a)).trans
    calc
      _ ≤ ∑a : Fin b → I,(1/(b.factorial:ℝ))*((2:ℝ)^D*(D:ℝ)^e*U^e*V^s) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [WeightedCoefficientSums.scalar_norm]
        exact mul_le_mul (ActivityFactorialSuppression.scalar_norm d) (hw a).2
          (WeightedCoefficientNorm.norm_nonnegative hr _) (by positivity)
      _ = _ := by simp [Fintype.card_fun]; ring
end StructuralActivityWeighted
#print axioms StructuralActivityWeighted.word_bound
