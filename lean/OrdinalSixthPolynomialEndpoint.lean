import OrdinalSixthPolynomial
noncomputable section
open Finset OrdinalSixthPolynomial

/-- Independent endpoint: the block polynomial identity, with all internal
coefficient definitions expanded. It is not a matrix theorem. -/
theorem finite_sixth_polynomial_endpoint (k : ℕ) (m f g Q L t : ℕ → ℝ)
    (n : ℝ) (hn : ∑ i ∈ range k, m i = n) :
    6*((∑ i ∈ range k, (g i/6-m i*f i-(m i*(m i^2-1)/3)^2/2+
          m i^3*(m i*(m i^2-1)/3)-m i^6/6)) +
        n*(∑ i ∈ range k, (f i-m i^2*(m i*(m i^2-1)/3)+m i^5/5)) +
        (∑ i ∈ range k, (m i^3/3-m i*(m i^2-1)/3))^2/2 -
        n^3*(∑ i ∈ range k, (m i^3/3-m i*(m i^2-1)/3))/3+n^6/45 -
      ((∑ i ∈ range k, ((g i-L i)/6-m i*(f i-Q i)-(m i*(m i^2-1)/3-8*t i)^2/2+
          m i^3*(m i*(m i^2-1)/3-8*t i)-m i^6/6)) +
        n*(∑ i ∈ range k, ((f i-Q i)-m i^2*(m i*(m i^2-1)/3-8*t i)+m i^5/5)) +
        (∑ i ∈ range k, (m i^3/3-(m i*(m i^2-1)/3-8*t i)))^2/2 -
        n^3*(∑ i ∈ range k, (m i^3/3-(m i*(m i^2-1)/3-8*t i)))/3+n^6/45)) =
    (∑ i ∈ range k, L i)+6*(∑ i ∈ range k, (n-m i)*Q i)+
      16*(∑ i ∈ range k, (n^3-3*n*m i^2+2*m i^3-n+m i)*t i)-
      384*(∑ i ∈ range k, ∑ j ∈ range i, t j*t i) := by
  exact coefficient_deficit_pairs k m f g Q L t n hn

#print axioms finite_sixth_polynomial_endpoint
#print axioms coefficient_deficit_pairs
#print axioms interaction_le_total_square
#print axioms small_block_bracket
#print axioms small_deficit_transfer
