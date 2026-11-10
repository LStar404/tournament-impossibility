import BalancedRawData
import ActualCoreWeightedBound
import RawPhysicalWeightedNorm

/-! Genuine core/activity bounds from actual dense doubly stochastic matrices. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace GeneralBalancedWeighted
open Matrix WeightedCoefficientNorm BalancedRawData RawFormalMixedSpecialization

def coordinateConstant (C rho s q : ℝ) : ℝ :=
  (s*(C+1)+2*s^2*(C+1)^2/(1-s*q))/(1-rho/s)
def coordinateScale (C rho s q : ℝ) : ℝ := max 1 (coordinateConstant C rho s q)
def coreConstant (C rho s q : ℝ) : ℝ := Real.exp (coordinateConstant C rho s q)
def activityConstant (C rho s q : ℝ) : ℝ :=
  QuantitativeFixedActivity.totalConstant (coordinateScale C rho s q)

def innerRadius (q : ℝ) : ℝ := 1+(1-q)/4
def outerRadius (q : ℝ) : ℝ := 1+(1-q)/2

lemma radius_data {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 < innerRadius q ∧ innerRadius q < outerRadius q ∧ outerRadius q*q < 1 := by
  unfold innerRadius outerRadius
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith [sq_nonneg (1-q)]

lemma coordinate_nonneg {C rho s q : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ rho)
    (hrs : rho < s) (hgap : s*q < 1) : 0 ≤ coordinateConstant C rho s q := by
  have hs : 0 < s := hr.trans_lt hrs
  have hd : 0 < 1-rho/s := sub_pos.mpr ((div_lt_one hs).mpr hrs)
  have hg : 0 < 1-s*q := sub_pos.mpr hgap
  unfold coordinateConstant
  positivity

lemma activity_pos (C rho s q : ℝ) : 0 < activityConstant C rho s q := by
  have hL : (1 : ℝ) ≤ coordinateScale C rho s q := le_max_left _ _
  have hLpos : 0 < coordinateScale C rho s q := zero_lt_one.trans_le hL
  unfold activityConstant QuantitativeFixedActivity.totalConstant
  positivity

section Actual
variable {m : ℕ} (hm : 0  <  m) (M : Matrix (Fin m) (Fin m) ℝ)
variable (C q rho s : ℝ) (hC : 0 ≤ C)
variable (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i j, M i j ≤ C/(m : ℝ))
variable (hr : ∀ i, (∑ j, M i j)=1) (hc : ∀ j, (∑ i, M i j)=1)
variable (hq : 0 ≤ q)
variable (hN : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M-ActualHessianFinite.P m)‖ ≤ q)
variable (hrho : 0 ≤ rho) (hrs : rho < s) (hgap : s*q < 1)
include hm hC hM hd hr hc hq hN hrho hrs hgap

/-- Both old physical series, with the mean norm exactly zero. -/
theorem coordinates :
    (∀ i j, Finite rho (PhysicalTiltedCovariance.covariance (block M) identityInteraction i j) ∧
      norm rho (PhysicalTiltedCovariance.covariance (block M) identityInteraction i j)
         ≤ coordinateConstant C rho s q/(m : ℝ)) ∧
    (∀ i, Finite rho (PhysicalTiltedCovariance.mean (block M) identityInteraction (fun _ => 1) i) ∧
      norm rho (PhysicalTiltedCovariance.mean (block M) identityInteraction (fun _ => 1) i)=0) := by
  have hw := RawPhysicalWeightedNorm.bounds hm (block M)
    hrho hrs (show 0 ≤ C+1 by linarith) (show (0 : ℝ) ≤ 0 by rfl)
    (block_norm M hq hN) hgap (block_entry hm M hC hM hd)
    (fun i => by rw [block_mulVec_one_zero hm M hr hc]; simp)
  constructor
  · intro i j
    refine ⟨(hw.1 i j).1, ?_⟩
    convert (hw.1 i j).2 using 1 <;> unfold coordinateConstant <;> ring
  · intro i
    refine ⟨(hw.2 i).1, le_antisymm ?_ (norm_nonnegative hrho _)⟩
    simpa using (hw.2 i).2

/-- Uniform norm bound on the original core, not a separately chosen branch. -/
theorem core_bound :
    Finite rho (ActualResidualFrozenFactorization.core (centeredComplex M)) ∧
    norm rho (ActualResidualFrozenFactorization.core (centeredComplex M)) ≤ coreConstant C rho s q := by
  have hw := coordinates hm M C q rho s hC hM hd hr hc hq hN hrho hrs hgap
  have hm0 : (m : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hdiag : (∑ i, norm rho (PhysicalTiltedCovariance.covariance (block M) identityInteraction i i))
       ≤ 2*coordinateConstant C rho s q := by
    calc
      _  ≤  ∑ _i : Fin m ⊕ Fin m, coordinateConstant C rho s q/(m : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hw.1 i i).2)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
        field_simp
        <;> ring
  have hmean : (∑ i, norm rho (PhysicalTiltedCovariance.mean (block M) identityInteraction (fun _ => 1) i))
       ≤ 2*(0 : ℝ) := by
    have hz : (∑ i, norm rho (PhysicalTiltedCovariance.mean (block M) identityInteraction (fun _ => 1) i))=0 :=
      Finset.sum_eq_zero (fun i _ => (hw.2 i).2)
    simpa using hz.le
  have h := ActualCoreWeightedBound.candidate_bound hrho (block M)
    (coordinateConstant C rho s q) 0
    (fun i => (hw.1 i i).1) (fun i => (hw.2 i).1) hdiag hmean
  rw [ActualResidualFrozenFactorization.core_formula]
  simpa only [block, coreConstant, add_zero] using h

/-- Every positive actual activity, under only the actual matrix hypotheses. -/
theorem activity_bound (j : ℕ) (hj : 1 ≤ j) :
    Finite rho (BinaryGraphActivityBound.rawActivity (centeredComplex M) j) ∧
    norm rho (BinaryGraphActivityBound.rawActivity (centeredComplex M) j) ≤ 
      (activityConstant C rho s q*(j : ℝ)/(m : ℝ))^j := by
  have hw := coordinates hm M C q rho s hC hM hd hr hc hq hN hrho hrs hgap
  have hL : (1 : ℝ) ≤ coordinateScale C rho s q := le_max_left _ _
  have hAL : coordinateConstant C rho s q ≤ coordinateScale C rho s q := le_max_right _ _
  unfold BinaryGraphActivityBound.rawActivity activityConstant
  apply QuantitativeFixedActivity.bound (n := m) hm (by simp; omega)
    (block M) identityInteraction (FullWickSquarefreeCompatibility.block_symm (centeredComplex M))
    ActualResidualFrozenFactorization.identity_symmetry (fun _ => 1) j hj
    rho (coordinateScale C rho s q) hrho hL
    (fun i j => (hw.1 i j).1) (fun i => (hw.2 i).1)
  · intro i j
    exact (hw.1 i j).2.trans (div_le_div_of_nonneg_right hAL (Nat.cast_nonneg m))
  · intro i
    rw [(hw.2 i).2]
    exact div_nonneg (zero_le_one.trans hL) (Nat.cast_nonneg m)

/-- Product bound needed by the finite p=0 recovery window. -/
theorem product_bound (j : ℕ) (hj : 1 ≤ j) :
    Finite rho (ActualResidualFrozenFactorization.core (centeredComplex M) *
      BinaryGraphActivityBound.rawActivity (centeredComplex M) j) ∧
    norm rho (ActualResidualFrozenFactorization.core (centeredComplex M) *
      BinaryGraphActivityBound.rawActivity (centeredComplex M) j) ≤ 
      coreConstant C rho s q*(activityConstant C rho s q*(j : ℝ)/(m : ℝ))^j := by
  have hG := core_bound hm M C q rho s hC hM hd hr hc hq hN hrho hrs hgap
  have hA := activity_bound hm M C q rho s hC hM hd hr hc hq hN hrho hrs hgap j hj
  refine ⟨finite_mul hrho hG.1 hA.1, ?_⟩
  exact (mul_bound hrho hG.1 hA.1).trans
    (mul_le_mul hG.2 hA.2 (norm_nonnegative hrho _) (Real.exp_pos _).le)
end Actual

/-- Radius greater than one and all core/activity product bounds, with no radius
or core/covariance certificate left among the input assumptions. -/
theorem actual_uniform_bounds {m : ℕ} (hm : 0  <  m) (M : Matrix (Fin m) (Fin m) ℝ)
    (C q : ℝ) (hC : 0 ≤ C) (hM : ∀ i j, 0 ≤ M i j)
    (hd : ∀ i j, M i j ≤ C/(m : ℝ))
    (hr : ∀ i, (∑ j, M i j)=1) (hc : ∀ j, (∑ i, M i j)=1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hN : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M-ActualHessianFinite.P m)‖ ≤ q) :
    1 < innerRadius q ∧
    (Finite (innerRadius q) (ActualResidualFrozenFactorization.core (centeredComplex M)) ∧
      norm (innerRadius q) (ActualResidualFrozenFactorization.core (centeredComplex M)) ≤ 
        coreConstant C (innerRadius q) (outerRadius q) q) ∧
    (∀ j, 1 ≤ j →
      Finite (innerRadius q) (ActualResidualFrozenFactorization.core (centeredComplex M) *
        BinaryGraphActivityBound.rawActivity (centeredComplex M) j) ∧
      norm (innerRadius q) (ActualResidualFrozenFactorization.core (centeredComplex M) *
        BinaryGraphActivityBound.rawActivity (centeredComplex M) j) ≤ 
        coreConstant C (innerRadius q) (outerRadius q) q *
          (activityConstant C (innerRadius q) (outerRadius q) q*(j : ℝ)/(m : ℝ))^j) := by
  have hs := radius_data hq0 hq1
  have hrho : 0 ≤ innerRadius q := (zero_lt_one.trans hs.1).le
  exact ⟨hs.1,
    core_bound hm M C q (innerRadius q) (outerRadius q) hC hM hd hr hc hq0 hN hrho hs.2.1 hs.2.2,
    fun j hj => product_bound hm M C q (innerRadius q) (outerRadius q) hC hM hd hr hc hq0 hN
      hrho hs.2.1 hs.2.2 j hj⟩

end GeneralBalancedWeighted
#check @GeneralBalancedWeighted.coordinates
#print axioms GeneralBalancedWeighted.coordinates
#check @GeneralBalancedWeighted.core_bound
#print axioms GeneralBalancedWeighted.core_bound
#check @GeneralBalancedWeighted.activity_bound
#print axioms GeneralBalancedWeighted.activity_bound
#check @GeneralBalancedWeighted.product_bound
#print axioms GeneralBalancedWeighted.product_bound
#check @GeneralBalancedWeighted.actual_uniform_bounds
#print axioms GeneralBalancedWeighted.actual_uniform_bounds
