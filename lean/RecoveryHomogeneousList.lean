import FiniteFactorialRecovery
noncomputable section
namespace RecoveryHomogeneousList

def coeff : List ℝ → ℕ → ℝ
  | [], a => if a=0 then 1 else 0
  | x::L,a => ∑i∈Finset.range (a+1),x^i*coeff L (a-i)

theorem zero (L : List ℝ) : coeff L 0=1 := by
  induction L with
  | nil => simp [coeff]
  | cons x L ih => simp [coeff,ih]

theorem nonnegative (L : List ℝ) (hL : ∀x∈L,0 ≤ x) (a : ℕ) : 0 ≤ coeff L a := by
  induction L generalizing a with
  | nil => simp [coeff]; positivity
  | cons x L ih =>
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (pow_nonneg (hL x (by simp)) _) (ih (fun y hy => hL y (by simp [hy])) _)

theorem cons_step (x : ℝ) (L : List ℝ) (a : ℕ) :
    coeff (x::L) (a+1)=coeff L (a+1)+x*coeff (x::L) a := by
  rw [coeff,Finset.sum_range_succ']
  simp only [pow_zero,one_mul,Nat.sub_zero]
  rw [add_comm]
  congr 1
  rw [coeff,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show a+1-(i+1)=a-i by omega,pow_succ]
  ring

theorem cons_le (x : ℝ) (L : List ℝ) (hx : 0 ≤ x) (hL : ∀y∈L,0 ≤ y) (a : ℕ) :
    coeff L a ≤ coeff (x::L) a := by
  have hh := Finset.single_le_sum
    (fun i (_ : i∈Finset.range (a+1)) => mul_nonneg (pow_nonneg hx i) (nonnegative L hL (a-i)))
    (show 0∈Finset.range (a+1) by simp)
  simpa only [pow_zero,one_mul,Nat.sub_zero,coeff] using hh

/-- One-step domination is enough for every fixed-order positive tail; no multidegree splitting is assumed. -/
theorem step (L : List ℝ) (hL : ∀x∈L,0 ≤ x) (a : ℕ) :
    coeff L (a+1) ≤ L.sum*coeff L a := by
  induction L with
  | nil => simp [coeff]
  | cons x L ih =>
    have hx := hL x (by simp)
    have ht : ∀y∈L,0 ≤ y := fun y hy => hL y (by simp [hy])
    have hs : 0 ≤ L.sum := List.sum_nonneg ht
    rw [cons_step,List.sum_cons]
    calc
      _ ≤ L.sum*coeff L a+x*coeff (x::L) a := by have hh := ih ht; linarith
      _ ≤ L.sum*coeff (x::L) a+x*coeff (x::L) a := by
        have hh := mul_le_mul_of_nonneg_left (cons_le x L hx ht a) hs
        linarith
      _ = _ := by ring

theorem shift_bound (L : List ℝ) (hL : ∀x∈L,0 ≤ x) (a p : ℕ) :
    coeff L (a+p) ≤ L.sum^p*coeff L a := by
  have hs : 0 ≤ L.sum := List.sum_nonneg hL
  induction p with
  | zero => simp
  | succ p ih =>
    calc
      _ ≤ L.sum*coeff L (a+p) := by simpa only [Nat.add_assoc] using step L hL (a+p)
      _ ≤ L.sum*(L.sum^p*coeff L a) := mul_le_mul_of_nonneg_left ih hs
      _ = _ := by rw [pow_succ]; ring

theorem bound (L : List ℝ) (hL : ∀x∈L,0 ≤ x) (a : ℕ) : coeff L a ≤ L.sum^a := by
  simpa [zero] using shift_bound L hL 0 a
end RecoveryHomogeneousList
#print axioms RecoveryHomogeneousList.shift_bound
