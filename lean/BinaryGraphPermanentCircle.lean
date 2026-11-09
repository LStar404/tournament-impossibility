import BinaryRawGraphWeighted
import PermanentCircleEnvelope

/-! Candidate, not yet compiled. A concrete fixed positive-depth graph circle bound.
The enumeration remains arbitrary; this does not identify the manuscript's canonical
popcount numbering or prove the final normalized path-count recovery. -/
noncomputable section
namespace BinaryGraphPermanentCircle
open Matrix BinaryBalancedTensor BinaryGraphTransport BinaryRawGraphWeighted
variable {C : Type*} [Fintype C] [DecidableEq C]

lemma branch_row_score {n : ℕ} (hn : 0 < n) (r : ℕ)
    (e : Bits (r+1) ≃ Fin (2^(r+1))) (B : Matrix C C ℝ)
    (f : Fin n ≃ C × Bits (r+1)) (v : ℝ) (hv : |v| ≤ 1)
    (i : Fin n) :
    ‖∑ j, TournamentSkewMargin.branch (realGraph (r+1) e B f) v i j‖ ≤
      ((2 : ℝ)^(r+1)+1)/(n : ℝ) := by
  have h := block_score hn r e B f v hv (Sum.inl i)
  simpa only [BipartiteOperatorBound.block, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, mul_one] using h

lemma branch_column_score {n : ℕ} (hn : 0 < n) (r : ℕ)
    (e : Bits (r+1) ≃ Fin (2^(r+1))) (B : Matrix C C ℝ)
    (f : Fin n ≃ C × Bits (r+1)) (v : ℝ) (hv : |v| ≤ 1)
    (j : Fin n) :
    ‖∑ i, TournamentSkewMargin.branch (realGraph (r+1) e B f) v i j‖ ≤
      ((2 : ℝ)^(r+1)+1)/(n : ℝ) := by
  have h := block_score hn r e B f v hv (Sum.inr j)
  simpa only [BipartiteOperatorBound.block, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, mul_one,
    Matrix.transpose_apply] using h

/-- Circle radius 5/4, with all raw entry, score and operator hypotheses discharged. -/
theorem envelope {n : ℕ} (hn : 24 ≤ n) (r : ℕ)
    (e : Bits (r+1) ≃ Fin (2^(r+1))) (B : Matrix C C ℝ)
    (hB : ∀ i j, B j i = -B i j) (he : ∀ i j, |B i j| ≤ 1)
    (f : Fin n ≃ C × Bits (r+1)) (v : ℝ) (hv : |v| ≤ 1)
    (z : ℂ) (hz : ‖z‖ ≤ 5/4) :
    ‖Matrix.permanent (PermanentSpectralFrame.averaging n +
      z • TournamentSkewMargin.branch (realGraph (r+1) e B f) v)‖ ≤
      ((n.factorial : ℝ)/(n : ℝ)^n) *
        Real.exp ((5/2)*((2 : ℝ)^(r+1)+1)+36*Real.sqrt (n : ℝ)) := by
  have hn0 : 0 < n := by omega
  have hsk : ∀ i j, realGraph (r+1) e B f j i = -realGraph (r+1) e B f i j := by
    intro i j
    simpa [realGraph] using congrArg Complex.re (graph_skew (r+1) e B hB (f i) (f j))
  have hen : ∀ i j, |realGraph (r+1) e B f i j| ≤ 1 := by
    intro i j
    exact (Complex.abs_re_le_norm _).trans (graph_entry (r+1) e B hB he (f i) (f j))
  have h := PermanentSpectralFrame.actual_permanent_circle_envelope hn0
    (TournamentSkewMargin.branch (realGraph (r+1) e B f) v) z
    (K:=((2 : ℝ)^(r+1)+1)) (C:=1) (T:=5/4) (q:=3/4)
    (by positivity) (by norm_num) (by norm_num) (by norm_num)
    (branch_row_score hn0 r e B f v hv) (branch_column_score hn0 r e B f v hv)
    (TournamentRawWeighted.branch_entry _ hsk hen v hv) hz
    (TournamentSkewMargin.branch_bound hn _ hsk hen v hv) (by norm_num)
  convert h using 1 <;> ring

/-- The same genuine bound after normalization by n!/n^n. -/
theorem normalized_envelope {n : ℕ} (hn : 24 ≤ n) (r : ℕ)
    (e : Bits (r+1) ≃ Fin (2^(r+1))) (B : Matrix C C ℝ)
    (hB : ∀ i j, B j i = -B i j) (he : ∀ i j, |B i j| ≤ 1)
    (f : Fin n ≃ C × Bits (r+1)) (v : ℝ) (hv : |v| ≤ 1)
    (z : ℂ) (hz : ‖z‖ ≤ 5/4) :
    ‖Matrix.permanent (PermanentSpectralFrame.averaging n +
      z • TournamentSkewMargin.branch (realGraph (r+1) e B f) v)‖ /
        ((n.factorial : ℝ)/(n : ℝ)^n) ≤
      Real.exp ((5/2)*((2 : ℝ)^(r+1)+1)+36*Real.sqrt (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (div_le_iff₀ (by positivity : 0 < (n.factorial : ℝ)/(n : ℝ)^n)).mpr
  simpa only [mul_comm] using envelope hn r e B hB he f v hv z hz
end BinaryGraphPermanentCircle
#print axioms BinaryGraphPermanentCircle.envelope
#print axioms BinaryGraphPermanentCircle.normalized_envelope
