import BinaryGraphTransport
noncomputable section
namespace BinaryRawGraphWeighted
open Matrix BinaryBalancedTensor BinaryGraphTransport
variable {C : Type*} [Fintype C] [DecidableEq C]

def realGraph {n : ℕ} (r : ℕ) (e : Bits r ≃ Fin (2^r))
    (B : Matrix C C ℝ) (f : Fin n ≃ C × Bits r) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (graph r e (ComplexifiedSkewBound.complexify B) (f i) (f j)).re

theorem branch_transport {n : ℕ} (r : ℕ) (e : Bits r ≃ Fin (2^r))
    (B : Matrix C C ℝ) (f : Fin n ≃ C × Bits r) (v : ℝ) (i j : Fin n) :
    TournamentSkewMargin.branch (realGraph r e B f) v i j=
      ((n:ℂ)⁻¹ • (graph r e (ComplexifiedSkewBound.complexify B)+(v:ℂ) •
        (1:Matrix (C × Bits r) (C × Bits r) ℂ))) (f i) (f j) := by
  simp only [TournamentSkewMargin.branch,realGraph,ComplexifiedSkewBound.complexify,
    Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,graph_real,Matrix.one_apply,
    f.injective.eq_iff]

theorem block_score {n : ℕ} (hn : 0<n) (r : ℕ) (e : Bits (r+1) ≃ Fin (2^(r+1)))
    (B : Matrix C C ℝ) (f : Fin n ≃ C × Bits (r+1)) (v : ℝ) (hv : |v| ≤ 1)
    (i : Fin n ⊕ Fin n) :
    ‖((BipartiteOperatorBound.block (TournamentSkewMargin.branch (realGraph (r+1) e B f) v)
      (TournamentSkewMargin.branch (realGraph (r+1) e B f) v).transpose).mulVec (fun _ => 1)) i‖ ≤
      ((2:ℝ)^(r+1)+1)/(n:ℝ) := by
  let A : Matrix (C × Bits (r+1)) (C × Bits (r+1)) ℂ :=
    (n:ℂ)⁻¹ • (graph (r+1) e (ComplexifiedSkewBound.complexify B)+(v:ℂ) • 1)
  have ht : ∀i j,TournamentSkewMargin.branch (realGraph (r+1) e B f) v i j=A (f i) (f j) :=
    branch_transport (r+1) e B f v
  have hbound : (((2:ℝ)^(r+1)+‖(v:ℂ)‖)/(n:ℝ)) ≤ ((2:ℝ)^(r+1)+1)/(n:ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    simpa using add_le_add_left hv ((2:ℝ)^(r+1))
  cases i with
  | inl i =>
    have h := branch_scores r e (ComplexifiedSkewBound.complexify B) (v:ℂ) n hn (f i)
    have heq : (∑j:Fin n,A (f i) (f j))=∑y:C × Bits (r+1),A (f i) y := f.sum_comp _
    simpa only [BipartiteOperatorBound.block,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,zero_mul,
      Finset.sum_const_zero,zero_add,mul_one,ht,heq] using h.trans hbound
  | inr i =>
    have h := branch_column_scores r e (ComplexifiedSkewBound.complexify B) (v:ℂ) n hn (f i)
    have heq : (∑j:Fin n,A (f j) (f i))=∑y:C × Bits (r+1),A y (f i) := f.sum_comp (fun y => A y (f i))
    simpa only [BipartiteOperatorBound.block,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,zero_mul,
      Finset.sum_const_zero,add_zero,mul_one,Matrix.transpose_apply,ht,heq] using h.trans hbound
/-- End-to-end fixed positive depth graph estimate, for the explicitly chosen enumeration.
No operator, inverse, analytic or score assumption is supplied by the caller. -/
theorem weighted {n : ℕ} (hn : 24 ≤ n) (r : ℕ)
    (e : Bits (r+1) ≃ Fin (2^(r+1))) (B : Matrix C C ℝ)
    (hB : ∀i j,B j i= -B i j) (he : ∀i j,|B i j| ≤ 1)
    (f : Fin n ≃ C × Bits (r+1)) (v : ℝ) (hv : |v| ≤ 1) :
    let S := realGraph (r+1) e B f
    let Q := BipartiteOperatorBound.block (TournamentSkewMargin.branch S v)
      (TournamentSkewMargin.branch S v).transpose
    (∀i j,WeightedCoefficientNorm.Finite (9/8) (PhysicalTiltedCovariance.covariance Q RawFormalMixedSpecialization.identityInteraction i j) ∧
      WeightedCoefficientNorm.norm (9/8) (PhysicalTiltedCovariance.covariance Q RawFormalMixedSpecialization.identityInteraction i j) ≤ (1025/2)/(n:ℝ)) ∧
    (∀i,WeightedCoefficientNorm.Finite (9/8) (PhysicalTiltedCovariance.mean Q RawFormalMixedSpecialization.identityInteraction (fun _ => 1) i) ∧
      WeightedCoefficientNorm.norm (9/8) (PhysicalTiltedCovariance.mean Q RawFormalMixedSpecialization.identityInteraction (fun _ => 1) i) ≤
        ((1025/2)*((2:ℝ)^(r+1)+1))/(n:ℝ)) := by
  have hsk : ∀i j,realGraph (r+1) e B f j i= -realGraph (r+1) e B f i j := by
    intro i j
    simpa [realGraph] using congrArg Complex.re (graph_skew (r+1) e B hB (f i) (f j))
  have hen : ∀i j,|realGraph (r+1) e B f i j| ≤ 1 := by
    intro i j
    exact (Complex.abs_re_le_norm _).trans (graph_entry (r+1) e B hB he (f i) (f j))
  exact TournamentRawWeighted.weighted hn _ hsk hen v hv _ (by positivity)
    (block_score (by omega) r e B f v hv)

end BinaryRawGraphWeighted
#print axioms BinaryRawGraphWeighted.weighted
