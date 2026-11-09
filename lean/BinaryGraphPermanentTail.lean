import BinaryGraphPermanentCircle
import PermanentActualCircleTail

/-! Genuine finite-polynomial tails for the explicitly enumerated positive-depth
binary graph family. This does not identify canonical popcount numbering or
assert the final path-count recovery theorem. -/
noncomputable section
namespace BinaryGraphPermanentTail
open Matrix BinaryBalancedTensor BinaryGraphTransport BinaryRawGraphWeighted
open PermanentSpectralFrame PermanentPolynomialCircleTail PermanentActualCircleTail
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Every fixed inverse power bounds the normalized true coefficient tail beyond
any positive linear cutoff. Constants are independent of n, v, and the base
matrix within the specified skew entry class, at fixed depth and cutoff. -/
theorem normalized_tail {n : ℕ} (hn : 24 ≤ n) (r : ℕ)
    (e : Bits (r+1) ≃ Fin (2^(r+1))) (B : Matrix C C ℝ)
    (hB : ∀ i j, B j i = -B i j) (he : ∀ i j, |B i j| ≤ 1)
    (f : Fin n ≃ C × Bits (r+1)) (v : ℝ) (hv : |v| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (p : ℕ) :
    (∑ k ∈ (permanentPolynomial (averaging n)
      (TournamentSkewMargin.branch (realGraph (r+1) e B f) v)).support.filter
      (fun k => ⌊δ*(n : ℝ)⌋₊ < k),
      ‖(permanentPolynomial (averaging n)
        (TournamentSkewMargin.branch (realGraph (r+1) e B f) v)).coeff k‖) /
        ((n.factorial : ℝ)/(n : ℝ)^n) ≤
      tailConstant ((2 : ℝ)^(r+1)+1) 1 (5/4) (3/4) δ p / (n : ℝ)^p := by
  have hn0 : 0 < n := by omega
  have hsk : ∀ i j, realGraph (r+1) e B f j i = -realGraph (r+1) e B f i j := by
    intro i j
    simpa [realGraph] using congrArg Complex.re (graph_skew (r+1) e B hB (f i) (f j))
  have hen : ∀ i j, |realGraph (r+1) e B f i j| ≤ 1 := by
    intro i j
    exact (Complex.abs_re_le_norm _).trans (graph_entry (r+1) e B hB he (f i) (f j))
  exact normalized_actual_tail_three_quarters hn0
    (TournamentSkewMargin.branch (realGraph (r+1) e B f) v)
    (by positivity) (by norm_num) hδ
    (BinaryGraphPermanentCircle.branch_row_score hn0 r e B f v hv)
    (BinaryGraphPermanentCircle.branch_column_score hn0 r e B f v hv)
    (TournamentRawWeighted.branch_entry _ hsk hen v hv)
    (TournamentSkewMargin.branch_bound hn _ hsk hen v hv) p

end BinaryGraphPermanentTail
#print axioms BinaryGraphPermanentTail.normalized_tail
