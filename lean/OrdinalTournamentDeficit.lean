import OrdinalSixthMatrixBridge
import TournamentSourceEnergy
import TransitiveFirstEnergy
import SmallBlockSixthEstimate
import TournamentEnergySeries
import ReferenceMomentComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OrdinalTournamentDeficit
open Finset Matrix VectorWeakMajorization TournamentPowerComparison OrdinalSixthPolynomial

def triangles {n : ℕ} (B : Tournament n) : ℝ :=
  (TournamentSourceEnergy.cycleCount B : ℝ)/3

def secondDeficit {n : ℕ} (B : Tournament n) : ℝ :=
  TwoBlockEnergy.second (TransitiveOrbit.T n)-TwoBlockEnergy.second (matrix B)
def sixthDeficit {n : ℕ} (B : Tournament n) : ℝ :=
  TwoBlockSixthMoment.third (TransitiveOrbit.T n)-TwoBlockSixthMoment.third (matrix B)

lemma triangles_nonneg {n : ℕ} (B : Tournament n) : 0 ≤ triangles B := by
  unfold triangles; positivity
lemma secondDeficit_nonneg {n : ℕ} (B : Tournament n) : 0 ≤ secondDeficit B := by
  apply sub_nonneg.mpr
  change TwoBlockEnergy.second (matrix B) ≤ TwoBlockEnergy.second (TransitiveOrbit.T n)
  unfold TwoBlockEnergy.second TwoBlockEnergy.ones
  simpa only [TournamentEnergySeries.energy, pow_two, Matrix.mulVec_mulVec] using
    TournamentEnergySeries.energy_le n 2 B
lemma sixthDeficit_nonneg {n : ℕ} (B : Tournament n) : 0 ≤ sixthDeficit B := by
  apply sub_nonneg.mpr
  simpa only [TwoBlockSixthMoment.third, RectangularFrobenius.sqnorm,
    RectangularFrobenius.inner, pow_two] using
    ReferenceMomentComparison.frobenius_all_powers n 3 B

/-- Difference from the actual ordered join of same-size transitive blocks.
The reference is an actual matrix, not an assumed total-order moment formula. -/
def actualDeficit (m : ℕ → ℕ) (B : ∀ i, Tournament (m i)) (k : ℕ) : ℝ :=
  TwoBlockSixthMoment.third
    (OrdinalBlockMatrix.matrix m (fun i => TransitiveOrbit.T (m i)) k) -
  TwoBlockSixthMoment.third
    (OrdinalBlockMatrix.matrix m (fun i => matrix (B i)) k)

/-- Actual tournament block sixth deficit with the genuine directed-cycle count
normalized by three. No source-energy/count identity is assumed. -/
theorem actual_deficit_formula (m : ℕ → ℕ) (B : ∀ i, Tournament (m i)) (k : ℕ) :
    actualDeficit m B k = SmallBlockSixthEstimate.deficit k
      (∑ i ∈ range k, (m i : ℝ)) (fun i => (m i : ℝ))
      (fun i => secondDeficit (B i)) (fun i => sixthDeficit (B i))
      (fun i => triangles (B i)) := by
  unfold actualDeficit
  rw [OrdinalSixthMatrixBridge.actual_sixth_coefficient m
        (fun i => TransitiveOrbit.T (m i)) (fun i => TransitiveOrbit.T_skew (m i)) k,
      OrdinalSixthMatrixBridge.actual_sixth_coefficient m
        (fun i => matrix (B i)) (fun i => (B i).skew) k]
  have hr : (fun i => TwoBlockEnergy.first (TransitiveOrbit.T (m i))) =
      (fun i => referenceFirst (m i : ℝ)) := by
    funext i
    exact TransitiveFirstEnergy.first_closed_form (m i)
  have he : (fun i => TwoBlockEnergy.first (matrix (B i))) =
      (fun i => referenceFirst (m i : ℝ)-8*triangles (B i)) := by
    funext i
    exact TournamentSourceEnergy.first_eq_reference_sub (B i)
  have hf : (fun i => TwoBlockEnergy.second (matrix (B i))) =
      (fun i => TwoBlockEnergy.second (TransitiveOrbit.T (m i))-secondDeficit (B i)) := by
    funext i; unfold secondDeficit; ring
  have hg : (fun i => TwoBlockSixthMoment.third (matrix (B i))) =
      (fun i => TwoBlockSixthMoment.third (TransitiveOrbit.T (m i))-sixthDeficit (B i)) := by
    funext i; unfold sixthDeficit; ring
  rw [hr, he, hf, hg, ← mul_sub]
  exact coefficient_deficit_pairs k (fun i => (m i : ℝ))
    (fun i => TwoBlockEnergy.second (TransitiveOrbit.T (m i)))
    (fun i => TwoBlockSixthMoment.third (TransitiveOrbit.T (m i)))
    (fun i => secondDeficit (B i)) (fun i => sixthDeficit (B i))
    (fun i => triangles (B i)) _ rfl

lemma triangle_upper {n : ℕ} (B : Tournament n) :
    24*triangles B ≤ (n : ℝ)^3 := by
  have he := TournamentSourceEnergy.first_eq_reference_sub B
  have hp : 0 ≤ TwoBlockEnergy.first (matrix B) := by
    unfold TwoBlockEnergy.first
    exact sum_nonneg (fun i _ => sq_nonneg _)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  change TwoBlockEnergy.first (matrix B) = _-8*triangles B at he
  nlinarith

/-- The triangle-total bound follows from actual source-energy nonnegativity;
it is not a graph-counting assumption. -/
lemma total_triangles_bound (m : ℕ → ℕ) (B : ∀ i, Tournament (m i))
    (k : ℕ) (n h : ℝ) (hnsize : ∑ i ∈ range k, (m i : ℝ) = n)
    (hh : 0 ≤ h) (hm : ∀ i ∈ range k, (m i : ℝ) ≤ h) :
    (∑ i ∈ range k, triangles (B i)) ≤ n*h^2/24 := by
  have hs : (∑ i ∈ range k, 24*triangles (B i)) ≤
      ∑ i ∈ range k, (m i : ℝ)*h^2 := by
    apply sum_le_sum
    intro i hi
    have ha : 0 ≤ (m i : ℝ) := Nat.cast_nonneg _
    have hb := hm i hi
    have hsq : (m i : ℝ)^2 ≤ h^2 := by nlinarith
    have hc := mul_le_mul_of_nonneg_left hsq ha
    have ht := triangle_upper (B i)
    nlinarith
  rw [← mul_sum, ← sum_mul, hnsize] at hs
  linarith

/-- Conditional graph application: the block-size and D bounds
are explicit. This theorem does not manufacture them from a diamond count. -/
theorem conditional_small_deficit (m : ℕ → ℕ) (B : ∀ i, Tournament (m i))
    (k : ℕ) (n h D : ℝ) (hnsize : ∑ i ∈ range k, (m i : ℝ) = n)
    (hn : 4 ≤ n) (hh : 0 ≤ h) (hhalf : 2*h ≤ n)
    (hm : ∀ i ∈ range k, (m i : ℝ) ≤ h)
    (hD : D ≤ (n-3)*(∑ i ∈ range k, triangles (B i))) :
    6*n^2*D ≤ actualDeficit m B k := by
  rw [actual_deficit_formula, hnsize]
  exact SmallBlockSixthEstimate.small_block_sixth k n h D _ _ _ _ hn hh hhalf
    (fun i hi => ⟨Nat.cast_nonneg _, hm i hi⟩)
    (fun i _ => secondDeficit_nonneg (B i))
    (fun i _ => sixthDeficit_nonneg (B i))
    (fun i _ => triangles_nonneg (B i))
    (total_triangles_bound m B k n h hnsize hh hm) hD
end OrdinalTournamentDeficit
#print axioms OrdinalTournamentDeficit.actual_deficit_formula
#print axioms OrdinalTournamentDeficit.conditional_small_deficit
