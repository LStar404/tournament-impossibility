import OrdinalSixthMatrixBridge
noncomputable section
open Finset Matrix
/-- Independent expanded endpoint for an actual finite real skew block family.
There is no assumed sixth-moment formula or determinant coefficient identity. -/
theorem actual_ordinal_sixth_expanded (m : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (hA : ∀ k i j, A k i j = -A k j i) (k : ℕ) :
    (∑ i, ∑ j, (((OrdinalBlockMatrix.matrix m A k)^3) i j)^2) =
    6*((∑ i ∈ range k,
        (TwoBlockSixthMoment.third (A i)/6-(m i : ℝ)*TwoBlockEnergy.second (A i)-
          (TwoBlockEnergy.first (A i))^2/2+(m i : ℝ)^3*TwoBlockEnergy.first (A i)-
          (m i : ℝ)^6/6)) +
      (∑ i ∈ range k, (m i : ℝ)) *
        (∑ i ∈ range k, (TwoBlockEnergy.second (A i)-
          (m i : ℝ)^2*TwoBlockEnergy.first (A i)+(m i : ℝ)^5/5)) +
      (∑ i ∈ range k, ((m i : ℝ)^3/3-TwoBlockEnergy.first (A i)))^2/2 -
      (∑ i ∈ range k, (m i : ℝ))^3 *
        (∑ i ∈ range k, ((m i : ℝ)^3/3-TwoBlockEnergy.first (A i)))/3 +
      (∑ i ∈ range k, (m i : ℝ))^6/45) := by
  simpa only [OrdinalSixthPolynomial.coefficient, OrdinalSixthPolynomial.cubic,
    OrdinalSixthPolynomial.quintic, TwoBlockSixthMoment.third,
    RectangularFrobenius.sqnorm, RectangularFrobenius.inner, pow_two] using
      OrdinalSixthMatrixBridge.actual_sixth_coefficient m A hA k
#print axioms actual_ordinal_sixth_expanded
#print axioms TwoBlockSixthMoment.third_join
#print axioms OrdinalSixthMatrixBridge.sixth_eq_cumulative
