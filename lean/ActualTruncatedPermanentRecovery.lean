import ActualGraphCoreRecovery
import PermanentTruncatedRecoveryAlgebra

/-! Complete finite truncated recovery for the actual normalized permanent.
The order condition is explicit. The evaluation estimate is on the closed unit
disk; no assertion about an untruncated infinite approximant is made. -/
noncomputable section
namespace ActualTruncatedPermanentRecovery
open ActualGraphCoreRecovery PermanentTruncatedRecoveryAlgebra
open PermanentNormalizedFrozenBridge

def tailConstant (d p : ℕ) : ℝ :=
  PermanentActualCircleTail.tailConstant ((2 : ℝ)^(d+1)+1) 1 (5/4) (3/4) (cutoff d) (p+1)
def errorConstant (d p : ℕ) : ℝ := lowConstant d p+highConstant d p+tailConstant d p

lemma degree_le (d n : ℕ) (hn : 0<n) : degree d n≤n := by
  have hb := budget d n (degree d n) hn (by simp [window])
  omega

section Graph
variable {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
variable (hn : 24≤n) (d : ℕ)
variable (e : BinaryBalancedTensor.Bits (d+1) ≃ Fin (2^(d+1))) (B : Matrix C C ℝ)
variable (hB : ∀ i j, B j i= -B i j) (he : ∀ i j, |B i j|≤1)
variable (f : Fin n ≃ C × BinaryBalancedTensor.Bits (d+1)) (v : ℝ) (hv : |v|≤1)
include hn hB he hv

/-- Complete coefficient error for the actual permanent and an explicitly
finite recovery polynomial. Both polynomials vanish above degree n. -/
theorem coefficient_error (p : ℕ) (hp : p≤degree d n) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    (∑ k∈Finset.range (n+1), ‖(normalized M).coeff k-
      (approximation M p (degree d n)).coeff k‖)≤errorConstant d p/(n : ℝ)^(p+1) := by
  let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
  have hmn := degree_le d n (by omega)
  have hw := finite_window_error M (by omega) p (degree d n) hp hmn
  have hL := low_sum hn d e B hB he f v hv p
  have hH := high_sum hn d e B hB he f v hv p
  have hT := PermanentNormalizedTailBridge.graph_tail hn d e B hB he f v hv (cutoff_pos d) (p+1)
  dsimp only at hL hH hT ⊢
  have hlow : (∑ k∈Finset.range (degree d n+1), ‖(normalized M).coeff k-
      (approximation M p (degree d n)).coeff k‖)≤
      (lowConstant d p+highConstant d p)/(n : ℝ)^(p+1) := by
    calc
      _ ≤ _ := hw
      _ ≤ lowConstant d p/(n : ℝ)^(p+1)+highConstant d p/(n : ℝ)^(p+1) :=
        add_le_add hL hH
      _ = _ := by ring
  change (∑ k∈Finset.range (n+1), ‖(normalized M).coeff k-
    (approximation M p (degree d n)).coeff k‖)≤errorConstant d p/(n : ℝ)^(p+1)
  rw [full_coefficient_split M p (degree d n) hmn]
  calc
    _ ≤ (lowConstant d p+highConstant d p)/(n : ℝ)^(p+1)+
        tailConstant d p/(n : ℝ)^(p+1) := add_le_add hlow hT
    _ = _ := by unfold errorConstant; ring

/-- Uniform on |z|≤1, with the depth-dependent finite cutoff kept explicit. -/
theorem evaluation_error (p : ℕ) (hp : p≤degree d n) (z : ℂ) (hz : ‖z‖≤1) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    ‖(normalized M).eval z-(approximation M p (degree d n)).eval z‖≤
      errorConstant d p/(n : ℝ)^(p+1) := by
  exact (eval_error_le_coefficients _ p (degree d n) (degree_le d n (by omega)) z hz).trans
    (coefficient_error hn d e B hB he f v hv p hp)

/-- Literal normalized permanent, rather than an independently defined proxy. -/
theorem actual_permanent_error (p : ℕ) (hp : p≤degree d n) (z : ℂ) (hz : ‖z‖≤1) :
    let M := TournamentSkewMargin.branch (BinaryRawGraphWeighted.realGraph (d+1) e B f) v
    ‖Matrix.permanent (fun i j => 1+(n : ℂ)*z*M i j)/(n.factorial : ℂ)-
      (approximation M p (degree d n)).eval z‖≤errorConstant d p/(n : ℝ)^(p+1) := by
  dsimp only
  rw [← PermanentNormalizedTailBridge.eval_actual _ (by omega) z]
  exact evaluation_error hn d e B hB he f v hv p hp z hz
end Graph
end ActualTruncatedPermanentRecovery
#print axioms ActualTruncatedPermanentRecovery.coefficient_error
#print axioms ActualTruncatedPermanentRecovery.evaluation_error
#print axioms ActualTruncatedPermanentRecovery.actual_permanent_error
