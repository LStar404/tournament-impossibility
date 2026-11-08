import Mathlib

noncomputable section
namespace OrdinalSixthPolynomial
open Finset

def referenceFirst (m : ℝ) : ℝ := m*(m^2-1)/3

def cubic {ι : Type*} (s : Finset ι) (m e : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (m i ^3/3-e i)

def quintic {ι : Type*} (s : Finset ι) (m e f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (f i-m i^2*e i+m i^5/5)

/-- A finite polynomial, not yet identified here with a matrix log-determinant. -/
def coefficient {ι : Type*} (s : Finset ι) (n : ℝ) (m e f g : ι → ℝ) : ℝ :=
  (∑ i ∈ s, (g i/6-m i*f i-e i^2/2+m i^3*e i-m i^6/6)) +
  n*quintic s m e f + (cubic s m e)^2/2-n^3*cubic s m e/3+n^6/45

lemma reference_cubic {ι : Type*} (s : Finset ι) (m : ι → ℝ) :
    cubic s m (fun i => referenceFirst (m i)) = (∑ i ∈ s, m i)/3 := by
  unfold cubic referenceFirst
  rw [sum_div]
  apply sum_congr rfl
  intro i hi
  ring

lemma shifted_cubic {ι : Type*} (s : Finset ι) (m t : ι → ℝ) :
    cubic s m (fun i => referenceFirst (m i)-8*t i) =
      (∑ i ∈ s, m i)/3+8*(∑ i ∈ s, t i) := by
  unfold cubic referenceFirst
  simp only [sum_div, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  ring

/-- Exact finite algebraic subtraction. The inputs f0,g0,Q,L,t are arbitrary real
arrays; no claim about actual tournament moments is hidden in this statement. -/
theorem coefficient_deficit {ι : Type*} (s : Finset ι)
    (m f0 g0 Q L t : ι → ℝ) (n : ℝ) (hn : ∑ i ∈ s, m i = n) :
    6*(coefficient s n m (fun i => referenceFirst (m i)) f0 g0 -
       coefficient s n m (fun i => referenceFirst (m i)-8*t i)
         (fun i => f0 i-Q i) (fun i => g0 i-L i)) =
    (∑ i ∈ s, L i)+6*(∑ i ∈ s, (n-m i)*Q i)+
      16*(∑ i ∈ s, (n^3-3*n*m i^2+2*m i^3-n+m i)*t i)+
      192*(∑ i ∈ s, (t i)^2)-192*(∑ i ∈ s, t i)^2 := by
  unfold coefficient
  rw [reference_cubic, shifted_cubic, hn]
  have hlocal :
      (∑ i ∈ s, (g0 i/6-m i*f0 i-(referenceFirst (m i))^2/2+
        m i^3*referenceFirst (m i)-m i^6/6)) -
      (∑ i ∈ s, ((g0 i-L i)/6-m i*(f0 i-Q i)-
        (referenceFirst (m i)-8*t i)^2/2+
        m i^3*(referenceFirst (m i)-8*t i)-m i^6/6)) =
      ∑ i ∈ s, (L i/6-m i*Q i+
        (m i^3-referenceFirst (m i))*8*t i+32*(t i)^2) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  have hquint : quintic s m (fun i => referenceFirst (m i)) f0 -
      quintic s m (fun i => referenceFirst (m i)-8*t i) (fun i => f0 i-Q i) =
      ∑ i ∈ s, (Q i-8*m i^2*t i) := by
    unfold quintic
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  calc
    _ = 6*((∑ i ∈ s, (L i/6-m i*Q i+
        (m i^3-referenceFirst (m i))*8*t i+32*(t i)^2)) +
        n*(∑ i ∈ s, (Q i-8*m i^2*t i))) +
        16*(n^3-n)*(∑ i ∈ s, t i)-192*(∑ i ∈ s, t i)^2 := by
      rw [← hlocal, ← hquint]
      ring
    _ = _ := by
      have hsum :
          6*((∑ i ∈ s, (L i/6-m i*Q i+
            (m i^3-referenceFirst (m i))*8*t i+32*(t i)^2)) +
            n*(∑ i ∈ s, (Q i-8*m i^2*t i))) +
            16*(n^3-n)*(∑ i ∈ s, t i) =
          (∑ i ∈ s, L i)+6*(∑ i ∈ s, (n-m i)*Q i)+
            16*(∑ i ∈ s, (n^3-3*n*m i^2+2*m i^3-n+m i)*t i)+
            192*(∑ i ∈ s, (t i)^2) := by
        simp only [mul_add, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro i hi
        unfold referenceFirst
        ring
      rw [hsum]

/-- Every unordered pair is counted once, with the earlier index first. -/
def pairInteraction (k : ℕ) (t : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range k, ∑ j ∈ range i, t j*t i

lemma total_square (k : ℕ) (t : ℕ → ℝ) :
    (∑ i ∈ range k, t i)^2 =
      (∑ i ∈ range k, (t i)^2)+2*pairInteraction k t := by
  induction k with
  | zero => simp [pairInteraction]
  | succ k ih =>
    simp only [pairInteraction, sum_range_succ] at ih ⊢
    rw [← sum_mul]
    nlinarith

/-- The exact ordered-block deficit polynomial, with the negative interaction
term expressed as an unordered-pair sum. This does NOT assert that an actual
matrix sixth moment equals six times `coefficient`; that bridge is separate. -/
theorem coefficient_deficit_pairs (k : ℕ) (m f0 g0 Q L t : ℕ → ℝ)
    (n : ℝ) (hn : ∑ i ∈ range k, m i = n) :
    6*(coefficient (range k) n m (fun i => referenceFirst (m i)) f0 g0 -
       coefficient (range k) n m (fun i => referenceFirst (m i)-8*t i)
         (fun i => f0 i-Q i) (fun i => g0 i-L i)) =
    (∑ i ∈ range k, L i)+6*(∑ i ∈ range k, (n-m i)*Q i)+
      16*(∑ i ∈ range k, (n^3-3*n*m i^2+2*m i^3-n+m i)*t i)-
      384*pairInteraction k t := by
  rw [coefficient_deficit (range k) m f0 g0 Q L t n hn, total_square]
  ring

lemma weight_factorization (n m : ℝ) :
    n^3-3*n*m^2+2*m^3-n+m = (n-m)*((n-m)^2+3*m*(n-m)-1) := by
  ring

lemma interaction_le_total_square (k : ℕ) (t : ℕ → ℝ) :
    2*pairInteraction k t ≤ (∑ i ∈ range k, t i)^2 := by
  rw [total_square]
  exact le_add_of_nonneg_left (sum_nonneg (fun i _ => sq_nonneg (t i)))

/-- Scalar estimate used after the graph-specific hypotheses have been proved. -/
lemma small_block_bracket (n h : ℝ) (hn : 0 ≤ n) (hh : 0 ≤ h)
    (hhalf : 2*h ≤ n) :
    6*n^3-16*n ≤ 16*n^3-56*n*h^2+32*h^3-16*n := by
  have hsq : 4*h^2 ≤ n^2 := by nlinarith [sq_nonneg (n-2*h)]
  have hp : 0 ≤ 5*n^2+10*n*h-8*h^2 := by
    nlinarith [mul_nonneg hn hh, sq_nonneg n]
  have hf := mul_nonneg (show 0 ≤ n-2*h by linarith) hp
  nlinarith

/-- No graph identity is hidden here: D, r and the prior lower bound are inputs. -/
lemma small_deficit_transfer (n h r D delta : ℝ) (hn : 4 ≤ n)
    (hh : 0 ≤ h) (hhalf : 2*h ≤ n) (hr : 0 ≤ r)
    (hD : D ≤ (n-3)*r)
    (hlower : (16*n^3-56*n*h^2+32*h^3-16*n)*r ≤ delta) :
    6*n^2*D ≤ delta := by
  have hn0 : 0 ≤ n := by linarith
  have hb := mul_le_mul_of_nonneg_right (small_block_bracket n h hn0 hh hhalf) hr
  have hd := mul_le_mul_of_nonneg_left hD (show 0 ≤ 6*n^2 by positivity)
  have hc : 0 ≤ (18*n^2-16*n)*r := by
    apply mul_nonneg _ hr
    nlinarith [sq_nonneg (n-4)]
  nlinarith

end OrdinalSixthPolynomial
