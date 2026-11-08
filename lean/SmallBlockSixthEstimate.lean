import OrdinalSixthPolynomial
noncomputable section
namespace SmallBlockSixthEstimate
open Finset OrdinalSixthPolynomial

def deficit (k : ℕ) (n : ℝ) (m Q L t : ℕ → ℝ) : ℝ :=
  (∑ i ∈ range k, L i)+6*(∑ i ∈ range k, (n-m i)*Q i)+
    16*(∑ i ∈ range k, (n^3-3*n*m i^2+2*m i^3-n+m i)*t i)-
    384*pairInteraction k t

lemma weight_lower (n h m : ℝ) (hm : 0 ≤ m) (hmh : m ≤ h) (hhn : h ≤ n) :
    n^3-3*n*h^2+2*h^3-n ≤ n^3-3*n*m^2+2*m^3-n+m := by
  have hh : 0 ≤ h := le_trans hm hmh
  have hp : 0 ≤ 3*n*(h+m)-2*(h^2+h*m+m^2) := by
    have h1 := mul_nonneg (show 0 ≤ n-h by linarith) (show 0 ≤ h+m by linarith)
    have h2 := mul_nonneg (show 0 ≤ h-m by linarith) (show 0 ≤ h+2*m by linarith)
    nlinarith
  have h3 := mul_nonneg (show 0 ≤ h-m by linarith) hp
  nlinarith

/-- Finite polynomial estimate. All block-count bounds remain explicit inputs. -/
theorem deficit_lower (k : ℕ) (n h : ℝ) (m Q L t : ℕ → ℝ)
    (hh : 0 ≤ h) (hhn : h ≤ n)
    (hm : ∀ i ∈ range k, 0 ≤ m i ∧ m i ≤ h)
    (hQ : ∀ i ∈ range k, 0 ≤ Q i) (hL : ∀ i ∈ range k, 0 ≤ L i)
    (ht : ∀ i ∈ range k, 0 ≤ t i)
    (htri : (∑ i ∈ range k, t i) ≤ n*h^2/24) :
    (16*n^3-56*n*h^2+32*h^3-16*n)*(∑ i ∈ range k, t i) ≤
      deficit k n m Q L t := by
  let r := ∑ i ∈ range k, t i
  have hr : 0 ≤ r := sum_nonneg ht
  have hls : 0 ≤ ∑ i ∈ range k, L i := sum_nonneg hL
  have hqs : 0 ≤ ∑ i ∈ range k, (n-m i)*Q i := by
    apply sum_nonneg
    intro i hi
    exact mul_nonneg (sub_nonneg.mpr (le_trans (hm i hi).2 hhn)) (hQ i hi)
  have hw : (n^3-3*n*h^2+2*h^3-n)*r ≤
      ∑ i ∈ range k, (n^3-3*n*m i^2+2*m i^3-n+m i)*t i := by
    dsimp [r]
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (weight_lower n h (m i) (hm i hi).1 (hm i hi).2 hhn) (ht i hi)
  have hp := interaction_le_total_square k t
  have hs := mul_le_mul_of_nonneg_right htri hr
  unfold deficit
  dsimp [r] at *
  nlinarith

/-- Conditional small-block conclusion, not a theorem asserting the required
triangle/diamond counts for a graph. -/
theorem small_block_sixth (k : ℕ) (n h D : ℝ) (m Q L t : ℕ → ℝ)
    (hn : 4 ≤ n) (hh : 0 ≤ h) (hhalf : 2*h ≤ n)
    (hm : ∀ i ∈ range k, 0 ≤ m i ∧ m i ≤ h)
    (hQ : ∀ i ∈ range k, 0 ≤ Q i) (hL : ∀ i ∈ range k, 0 ≤ L i)
    (ht : ∀ i ∈ range k, 0 ≤ t i)
    (htri : (∑ i ∈ range k, t i) ≤ n*h^2/24)
    (hD : D ≤ (n-3)*(∑ i ∈ range k, t i)) :
    6*n^2*D ≤ deficit k n m Q L t := by
  exact small_deficit_transfer n h _ D _ hn hh hhalf (sum_nonneg ht) hD
    (deficit_lower k n h m Q L t hh (by linarith) hm hQ hL ht htri)
end SmallBlockSixthEstimate
#print axioms SmallBlockSixthEstimate.small_block_sixth
