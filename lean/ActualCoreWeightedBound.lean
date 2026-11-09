import WeightedFormalExponential
import ActualCoreTracePrimitive
import BinaryGraphActivityBound

/-!
Fixed positive-depth uniform bound for the original actual core, obtained
from the proved actual covariance/mean weighted bounds.
No diamond-free, extra inverse, or externally assumed core bound is used.
-/
noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ActualCoreWeightedBound
open Matrix WeightedCoefficientNorm ActualCoreTracePrimitive RawFormalMixedSpecialization
variable {I : Type*} [Fintype I]

lemma primitive_mass {s : ℝ} (hs : 0 ≤ s) (T : PowerSeries ℂ) (k : ℕ) :
    mass s (primitive T) k ≤ (1/2 : ℝ)*mass s T k := by
  by_cases hk : k=0
  · subst k
    simp only [mass, primitive, PowerSeries.coeff_mk, Nat.cast_zero, mul_zero,
      div_zero, norm_zero, zero_mul, pow_zero, mul_one]
    positivity
  · have hk1 : (1 : ℝ)≤k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    have hb : ‖(primitive T).coeff k‖ ≤ ‖T.coeff k‖/2 := by
      simp only [primitive, PowerSeries.coeff_mk, norm_div, norm_neg, norm_mul,
        Complex.norm_natCast]
      norm_num only [Complex.norm_ofNat]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)
    have hh := mul_le_mul_of_nonneg_right hb (pow_nonneg hs k)
    simpa only [mass, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_mul, mul_one] using hh

lemma primitive_bound {s : ℝ} (hs : 0 ≤ s) (T : PowerSeries ℂ)
    (hT : Finite s T) :
    Finite s (primitive T) ∧ norm s (primitive T) ≤ norm s T/2 := by
  have hmajor : Summable (fun k => (1/2 : ℝ)*mass s T k) := hT.mul_left _
  have hf : Finite s (primitive T) :=
    hmajor.of_nonneg_of_le (nonneg hs _) (primitive_mass hs T)
  refine ⟨hf, ?_⟩
  have hb := hf.tsum_le_tsum (primitive_mass hs T) hmajor
  simpa only [WeightedCoefficientNorm.norm, tsum_mul_left, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hb

lemma trace_finite {s : ℝ} (hs : 0 ≤ s) (Q : I → I → ℂ)
    (hW : ∀ i, Finite s (PhysicalTiltedCovariance.covariance Q identityInteraction i i)) :
    Finite s (covarianceTrace Q) := by
  exact WeightedCoefficientSums.sum_finite Finset.univ
    (fun i => PhysicalTiltedCovariance.covariance Q identityInteraction i i) hs
    (fun i hi => hW i)

lemma trace_bound {s : ℝ} (hs : 0 ≤ s) (Q : I → I → ℂ)
    (hW : ∀ i, Finite s (PhysicalTiltedCovariance.covariance Q identityInteraction i i)) :
    norm s (covarianceTrace Q) ≤
      ∑ i, norm s (PhysicalTiltedCovariance.covariance Q identityInteraction i i) := by
  exact WeightedCoefficientSums.sum_norm Finset.univ
    (fun i => PhysicalTiltedCovariance.covariance Q identityInteraction i i) hs
    (fun i hi => hW i)

lemma source_bound {s : ℝ} (hs : 0 ≤ s) (Q : I → I → ℂ)
    (heta : ∀ i, Finite s (PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1) i)) :
    Finite s (MixedEvenCandidate.source Q identityInteraction (fun _ => 1)) ∧
    norm s (MixedEvenCandidate.source Q identityInteraction (fun _ => 1)) ≤
      (∑ i, norm s (PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1) i))/2 := by
  have hf := WeightedCoefficientSums.sum_finite Finset.univ
    (fun i => PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1) i) hs
    (fun i hi => heta i)
  have hb := WeightedCoefficientSums.sum_norm Finset.univ
    (fun i => PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1) i) hs
    (fun i hi => heta i)
  rw [source_eq_half_mean]
  refine ⟨WeightedCoefficientSums.scalar_finite s _ _ hf, ?_⟩
  rw [WeightedCoefficientSums.scalar_norm]
  have hc : ‖(1/2 : ℂ)‖=(1/2 : ℝ) := by norm_num
  rw [hc]
  have hh := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ)≤1/2)
  simpa only [div_eq_mul_inv, mul_comm, one_mul, mul_one] using hh

/-- A generic finite-coordinate endpoint, used below for the existing actual core. -/
theorem candidate_bound {s : ℝ} (hs : 0 ≤ s) (Q : I → I → ℂ) (A U : ℝ)
    (hW : ∀ i, Finite s (PhysicalTiltedCovariance.covariance Q identityInteraction i i))
    (heta : ∀ i, Finite s (PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1) i))
    (bW : (∑ i, norm s (PhysicalTiltedCovariance.covariance Q identityInteraction i i))≤2*A)
    (beta : (∑ i, norm s (PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1) i))≤2*U) :
    Finite s (MixedEvenCandidate.candidate Q identityInteraction (fun _ => 1)) ∧
      norm s (MixedEvenCandidate.candidate Q identityInteraction (fun _ => 1))≤Real.exp (A+U) := by
  have hp := primitive_bound hs (covarianceTrace Q) (trace_finite hs Q hW)
  have hlog : norm s (logBranch Q)≤A := by
    have ht := (trace_bound hs Q hW).trans bW
    change norm s (primitive (covarianceTrace Q))≤A
    linarith [hp.2]
  have hsource := source_bound hs Q heta
  have hsourceBound : norm s (MixedEvenCandidate.source Q identityInteraction (fun _ => 1))≤U := by
    linarith [hsource.2]
  have heL := WeightedFormalExponential.bound hs (logBranch Q) (log_constant Q) hp.1
  have heS := WeightedFormalExponential.bound hs
    (MixedEvenCandidate.source Q identityInteraction (fun _ => 1))
    (MixedEvenCandidate.source_constant Q identityInteraction (fun _ => 1)) hsource.1
  rw [MixedEvenCandidate.candidate, branch_eq_exp]
  change Finite s (ZeroConstantFormalExp.expOf (logBranch Q)*
      ZeroConstantFormalExp.expOf (MixedEvenCandidate.source Q identityInteraction (fun _ => 1))) ∧ _
  refine ⟨finite_mul hs heL.1 heS.1, ?_⟩
  calc
    _ ≤ norm s (ZeroConstantFormalExp.expOf (logBranch Q))*
        norm s (ZeroConstantFormalExp.expOf (MixedEvenCandidate.source Q identityInteraction (fun _ => 1))) :=
      mul_bound hs heL.1 heS.1
    _ ≤ Real.exp (norm s (logBranch Q))*
        Real.exp (norm s (MixedEvenCandidate.source Q identityInteraction (fun _ => 1))) :=
      mul_le_mul heL.2 heS.2 (norm_nonnegative hs _) (Real.exp_pos _).le
    _ ≤ Real.exp A*Real.exp U :=
      mul_le_mul (Real.exp_le_exp.mpr hlog) (Real.exp_le_exp.mpr hsourceBound)
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

def coreConstant (depth : ℕ) : ℝ :=
  Real.exp ((1025/2)*((2 : ℝ)^(depth+1)+2))

/-- The fixed-depth bound is uniform over every permitted coarse skew matrix.
It does not infer that the constructed graph has zero diamonds. -/
theorem graph {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (hn : 24≤n) (depth : ℕ)
    (e : BinaryBalancedTensor.Bits (depth+1) ≃ Fin (2^(depth+1))) (B : Matrix C C ℝ)
    (hB : ∀ i j, B j i= -B i j) (he : ∀ i j, |B i j|≤1)
    (f : Fin n ≃ C × BinaryBalancedTensor.Bits (depth+1)) (v : ℝ) (hv : |v|≤1) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (depth+1) e B f) v
    Finite (9/8) (ActualResidualFrozenFactorization.core M) ∧
      norm (9/8) (ActualResidualFrozenFactorization.core M)≤coreConstant depth := by
  let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (depth+1) e B f) v
  let Q := FullWickSquarefreeCompatibility.block M
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hw := BinaryRawGraphWeighted.weighted hn depth e B hB he f v hv
  dsimp only at hw
  rw [← BinaryGraphActivityBound.block_eq] at hw
  change (∀ i j, Finite (9/8) (PhysicalTiltedCovariance.covariance Q identityInteraction i j) ∧
      norm (9/8) (PhysicalTiltedCovariance.covariance Q identityInteraction i j)≤(1025/2)/(n : ℝ)) ∧
    (∀ i, Finite (9/8) (PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1) i) ∧
      norm (9/8) (PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1) i)≤
        BinaryGraphActivityBound.coordinateConstant depth/(n : ℝ)) at hw
  have hd : (∑ i, norm (9/8) (PhysicalTiltedCovariance.covariance Q identityInteraction i i))≤
      2*(1025/2 : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n ⊕ Fin n, (1025/2 : ℝ)/(n : ℝ) :=
        Finset.sum_le_sum (fun i hi => (hw.1 i i).2)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
        field_simp
        <;> ring
  have hm : (∑ i, norm (9/8) (PhysicalTiltedCovariance.mean Q identityInteraction (fun _ => 1) i))≤
      2*BinaryGraphActivityBound.coordinateConstant depth := by
    calc
      _ ≤ ∑ _i : Fin n ⊕ Fin n, BinaryGraphActivityBound.coordinateConstant depth/(n : ℝ) :=
        Finset.sum_le_sum (fun i hi => (hw.2 i).2)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
        field_simp
        <;> ring
  have hc := candidate_bound (by norm_num : (0 : ℝ)≤9/8) Q (1025/2)
    (BinaryGraphActivityBound.coordinateConstant depth)
    (fun i => (hw.1 i i).1) (fun i => (hw.2 i).1) hd hm
  change Finite (9/8) (ActualResidualFrozenFactorization.core M) ∧
    norm (9/8) (ActualResidualFrozenFactorization.core M)≤coreConstant depth
  rw [ActualResidualFrozenFactorization.core_formula]
  have hconst : Real.exp ((1025/2 : ℝ)+BinaryGraphActivityBound.coordinateConstant depth)=
      coreConstant depth := by
    unfold BinaryGraphActivityBound.coordinateConstant coreConstant
    congr 1
    ring
  simpa only [hconst] using hc

end ActualCoreWeightedBound
#print axioms ActualCoreWeightedBound.candidate_bound
#print axioms ActualCoreWeightedBound.graph
