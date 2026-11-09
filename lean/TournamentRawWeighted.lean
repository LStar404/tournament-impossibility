import BipartiteOperatorBound
import RawPhysicalWeightedNorm
noncomputable section
namespace TournamentRawWeighted
open Matrix

theorem branch_entry {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (v : ℝ) (hv : |v| ≤ 1) (i j : Fin n) :
    ‖TournamentSkewMargin.branch S v i j‖ ≤ 1/(n:ℝ) := by
  have hd : S i i=0 := by have h := hS i i; linarith
  simp only [TournamentSkewMargin.branch,Matrix.smul_apply,Matrix.add_apply,
    smul_eq_mul,norm_mul,norm_inv,Complex.norm_natCast]
  have hh : ‖ComplexifiedSkewBound.complexify S i j+(v:ℂ)*(1:Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ 1 := by
    by_cases h : i=j
    · subst j; simpa [ComplexifiedSkewBound.complexify,hd,Matrix.one_apply] using hv
    · simpa [ComplexifiedSkewBound.complexify,Matrix.one_apply,h] using he i j
  simpa using mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Nat.cast_nonneg n))

theorem block_entry {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (v : ℝ) (hv : |v| ≤ 1) (i j : Fin n ⊕ Fin n) :
    ‖BipartiteOperatorBound.block (TournamentSkewMargin.branch S v)
      (TournamentSkewMargin.branch S v).transpose i j‖ ≤ 1/(n:ℝ) := by
  cases i <;> cases j
  · simp [BipartiteOperatorBound.block]
  · exact branch_entry S hS he v hv _ _
  · exact branch_entry S hS he v hv _ _
  · simp [BipartiteOperatorBound.block]

/-- Genuine tournament spectral hypotheses remove the former arbitrary q and disk assumptions.
The bounded raw score hypothesis is still explicit; it is not implied by diamond-freeness. -/
theorem weighted {n : ℕ} (hn : 24 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j,S j i= -S i j) (he : ∀ i j,|S i j| ≤ 1)
    (v : ℝ) (hv : |v| ≤ 1) (K : ℝ) (hK : 0 ≤ K)
    (hs : ∀i,‖((BipartiteOperatorBound.block (TournamentSkewMargin.branch S v)
      (TournamentSkewMargin.branch S v).transpose).mulVec (fun _ => 1)) i‖ ≤ K/(n:ℝ)) :
    let Q := BipartiteOperatorBound.block (TournamentSkewMargin.branch S v)
      (TournamentSkewMargin.branch S v).transpose
    (∀i j,WeightedCoefficientNorm.Finite (9/8) (PhysicalTiltedCovariance.covariance Q RawFormalMixedSpecialization.identityInteraction i j) ∧
      WeightedCoefficientNorm.norm (9/8) (PhysicalTiltedCovariance.covariance Q RawFormalMixedSpecialization.identityInteraction i j) ≤ (1025/2)/(n:ℝ)) ∧
    (∀i,WeightedCoefficientNorm.Finite (9/8) (PhysicalTiltedCovariance.mean Q RawFormalMixedSpecialization.identityInteraction (fun _ => 1) i) ∧
      WeightedCoefficientNorm.norm (9/8) (PhysicalTiltedCovariance.mean Q RawFormalMixedSpecialization.identityInteraction (fun _ => 1) i) ≤ ((1025/2)*K)/(n:ℝ)) := by
  dsimp only
  have h := RawPhysicalWeightedNorm.bounds (n:=n) (by omega) _
    (rho:=9/8) (s:=5/4) (q:=3/4) (C:=1) (K:=K)
    (by norm_num) (by norm_num) (by norm_num) hK
    (BipartiteOperatorBound.tournament_bound hn S hS he v hv) (by norm_num)
    (block_entry S hS he v hv) hs
  constructor
  · intro i j
    refine ⟨(h.1 i j).1, ?_⟩
    convert (h.1 i j).2 using 1 <;> ring
  · intro i
    refine ⟨(h.2 i).1, ?_⟩
    convert (h.2 i).2 using 1 <;> ring
end TournamentRawWeighted
#print axioms TournamentRawWeighted.weighted
