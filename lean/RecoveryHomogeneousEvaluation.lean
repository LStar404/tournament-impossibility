import RecoveryHomogeneousList
noncomputable section
namespace RecoveryHomogeneousEvaluation
open RecoveryHomogeneousList

def product (L : List ℝ) (z : ℝ) : ℝ := (L.map (fun x => (1-x*z)⁻¹)).prod

theorem scaled_cons (x : ℝ) (L : List ℝ) (z : ℝ) (a : ℕ) :
    coeff (x::L) a*z^a=∑i∈Finset.range (a+1),(x*z)^i*(coeff L (a-i)*z^(a-i)) := by
  rw [coeff,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ a := by simpa using hi
  rw [show z^a=z^i*z^(a-i) by rw [← pow_add,show i+(a-i)=a by omega],mul_pow]
  ring

theorem hasSum (L : List ℝ) (z : ℝ) (hz : 0 ≤ z)
    (hL : ∀x∈L,0 ≤ x ∧ x*z<1) :
    HasSum (fun a => coeff L a*z^a) (product L z) := by
  induction L with
  | nil =>
      convert (hasSum_ite_eq (0:ℕ) (1:ℝ)) using 1
      · funext a; by_cases ha : a=0 <;> simp [coeff,ha]
      · simp [product]
  | cons x L ih =>
    have hx := hL x (by simp)
    have ht := ih (fun y hy => hL y (by simp [hy]))
    have hg := hasSum_geometric_of_norm_lt_one (show ‖x*z‖<1 by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx.1 hz)]
      exact hx.2)
    have hc := hasSum_sum_range_mul_of_summable_norm hg.summable.norm ht.summable.norm
    rw [hg.tsum_eq,ht.tsum_eq] at hc
    simpa only [← scaled_cons,product,List.map_cons,List.prod_cons] using hc

/-- True positive remainder of the evaluated finite geometric product, for any fixed order. -/
theorem remainder (L : List ℝ) (z : ℝ) (hz : 0 ≤ z)
    (hL : ∀x∈L,0 ≤ x ∧ x*z<1) (p : ℕ) :
    0 ≤ product L z-∑a∈Finset.range (p+1),coeff L a*z^a ∧
    product L z-∑a∈Finset.range (p+1),coeff L a*z^a ≤
      product L z*(L.sum*z)^(p+1) := by
  have hn : ∀x∈L,0 ≤ x := fun x hx => (hL x hx).1
  have hh := hasSum L z hz hL
  have hs := hh.summable
  have ht := (summable_nat_add_iff (p+1)).mpr hs
  have he : product L z-∑a∈Finset.range (p+1),coeff L a*z^a=
      ∑'a,coeff L (a+(p+1))*z^(a+(p+1)) := by
    have hsum := hs.sum_add_tsum_nat_add (p+1)
    rw [hh.tsum_eq] at hsum
    linarith
  rw [he]
  constructor
  · exact tsum_nonneg (fun a => mul_nonneg (nonnegative L hn _) (pow_nonneg hz _))
  · have hb (a : ℕ) : coeff L (a+(p+1))*z^(a+(p+1)) ≤
        (L.sum*z)^(p+1)*(coeff L a*z^a) := by
      have h := mul_le_mul_of_nonneg_right (shift_bound L hn a (p+1)) (pow_nonneg hz (a+(p+1)))
      simpa only [pow_add,mul_pow,mul_assoc,mul_comm,mul_left_comm] using h
    have hu := ht.tsum_le_tsum hb (hs.mul_left ((L.sum*z)^(p+1)))
    rw [tsum_mul_left,hh.tsum_eq] at hu
    simpa only [mul_comm] using hu
end RecoveryHomogeneousEvaluation
#print axioms RecoveryHomogeneousEvaluation.remainder
