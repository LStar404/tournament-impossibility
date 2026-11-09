import ActivityNumericalBound
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semiring

/-! Finite activity-window estimates.  This file does not assert convergence of
an infinite activity expansion.  The cutoff depends on the activity constant D,
not only on the factorial-recovery radius.  The cutoff is explicitly depth dependent in the graph application. -/
noncomputable section
namespace ActivityFiniteWindowBound

/-- The numerical majorant supplied by `BinaryGraphActivityBound.bound`. -/
def term (D : ℝ) (n j : ℕ) : ℝ := (D*(j:ℝ)/(n:ℝ))^j

lemma one_plus_inverse_power (j : ℕ) (hj : 0 < j) :
    (1+1/(j:ℝ))^j ≤ Real.exp 1 := by
  have hjR : (0:ℝ)<j := by exact_mod_cast hj
  calc
    _ ≤ (Real.exp (1/(j:ℝ)))^j := pow_le_pow_left₀ (by positivity)
      (by simpa only [add_comm] using Real.add_one_le_exp (1/(j:ℝ))) j
    _ = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp

lemma term_successor (D : ℝ) (n j : ℕ) (hj : 0<j) :
    term D n (j+1) =
      (D*((j:ℝ)+1)/(n:ℝ))*(1+1/(j:ℝ))^j*term D n j := by
  have hj0 : (j:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hbase : D*((j:ℝ)+1)/(n:ℝ) =
      (1+1/(j:ℝ))*(D*(j:ℝ)/(n:ℝ)) := by
    field_simp
    <;> ring
  simp only [term, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [hbase, mul_pow]
  ring

/-- A real budget avoids floor manipulations inside the numerical estimate. -/
lemma term_half_step {D : ℝ} (hD : 0≤D) {n m j : ℕ}
    (hn : 0<n) (hj : 0<j) (hjm : j < m)
    (hbudget : 4*Real.exp 1*D*(m:ℝ) ≤ (n:ℝ)) :
    term D n (j+1) ≤ term D n j / 2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hjmR : (j:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hjm)
  have hterm : 0≤term D n j := by unfold term; positivity
  have hsmall : (D*((j:ℝ)+1)/(n:ℝ))*Real.exp 1 ≤ (1:ℝ)/4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hjmR
      (show 0≤4*Real.exp 1*D by positivity)]
  calc
    _ = (D*((j:ℝ)+1)/(n:ℝ))*(1+1/(j:ℝ))^j*term D n j :=
      term_successor D n j hj
    _ ≤ (D*((j:ℝ)+1)/(n:ℝ))*Real.exp 1*term D n j := by
      gcongr
      exact one_plus_inverse_power j hj
    _ ≤ (1/4:ℝ)*term D n j := mul_le_mul_of_nonneg_right hsmall hterm
    _ ≤ term D n j/2 := by linarith

/-- A finite geometric estimate, with no assumption on values after the window. -/
lemma finite_half_sum (f : ℕ → ℝ) (hf : ∀j, 0≤f j) (L : ℕ) :
    ∀s, (∀j, s≤j → j+1<s+L → f (j+1)≤f j/2) →
      (∑i ∈ Finset.range L, f (s+i)) ≤ 2*f s := by
  induction L with
  | zero => intro s hs; simpa using mul_nonneg (by norm_num : (0:ℝ)≤2) (hf s)
  | succ L ih =>
    intro s hs
    by_cases hL : L=0
    · subst L
      simpa using (show f s ≤ 2*f s by linarith [hf s])
    have ht := ih (s+1) (fun j hj htop => hs j (by omega) (by omega))
    have hfirst := hs s (le_refl s) (by omega)
    rw [Finset.sum_range_succ']
    have heq : (∑i ∈ Finset.range L, f (s+(i+1))) =
        ∑i ∈ Finset.range L, f ((s+1)+i) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    rw [heq]
    simp only [Nat.add_zero]
    linarith

/-- Tail of the activity window: empty windows are included automatically. -/
theorem sum_window {D : ℝ} (hD : 0≤D) (n m p : ℕ) (hn : 0<n)
    (hbudget : 4*Real.exp 1*D*(m:ℝ) ≤ (n:ℝ)) :
    (∑j ∈ Finset.Ico (p+1) (m+1), term D n j) ≤
      2*(D*((p:ℝ)+1))^(p+1)/(n:ℝ)^(p+1) := by
  have hf : ∀j, 0≤term D n j := by intro j; unfold term; positivity
  have hsum := finite_half_sum (term D n) hf (m+1-(p+1)) (p+1)
  have hstep : ∀j, p+1≤j → j+1<(p+1)+(m+1-(p+1)) →
      term D n (j+1)≤term D n j/2 := by
    intro j hj ht
    exact term_half_step hD hn (by omega) (by omega) hbudget
  have h := hsum hstep
  rw [← Finset.sum_Ico_eq_sum_range] at h
  calc
    _ ≤ 2*term D n (p+1) := h
    _ = _ := by simp only [term, Nat.cast_add, Nat.cast_one, div_pow]; ring

/-- The explicit depth-dependent cutoff.  In applications take D to be the
constant from `BinaryGraphActivityBound.bound`, and take the minimum of this
cutoff and the independent factorial-recovery cutoff. -/
theorem sum_floor_window {D α : ℝ} (hD : 0<D) (hα : 0≤α)
    (hαD : α≤1/(4*Real.exp 1*D)) (n p : ℕ) (hn : 0<n) :
    (∑j ∈ Finset.Ico (p+1) (⌊α*(n:ℝ)⌋₊+1), term D n j) ≤
      2*(D*((p:ℝ)+1))^(p+1)/(n:ℝ)^(p+1) := by
  apply sum_window hD.le n _ p hn
  have hpos : 0<4*Real.exp 1*D := by positivity
  have hαbound : (4*Real.exp 1*D)*α ≤ 1 := by
    have := (le_div_iff₀ hpos).mp hαD
    nlinarith
  have hfloor : (⌊α*(n:ℝ)⌋₊:ℝ) ≤ α*(n:ℝ) :=
    Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg n))
  calc
    _ ≤ (4*Real.exp 1*D)*(α*(n:ℝ)) :=
      mul_le_mul_of_nonneg_left hfloor hpos.le
    _ = ((4*Real.exp 1*D)*α)*(n:ℝ) := by ring
    _ ≤ 1*(n:ℝ) := mul_le_mul_of_nonneg_right hαbound (Nat.cast_nonneg n)
    _ = _ := one_mul _

/-- The same bound for any nonnegative sequence bounded termwise by the actual
activity majorant, ready for weighted norms once the core product is bounded. -/
theorem dominated_floor_window {D α B : ℝ} (hD : 0<D) (hα : 0≤α)
    (hαD : α≤1/(4*Real.exp 1*D)) (hB : 0≤B) (n p : ℕ) (hn : 0<n)
    (a : ℕ → ℝ)
    (ha : ∀j ∈ Finset.Ico (p+1) (⌊α*(n:ℝ)⌋₊+1), a j≤B*term D n j) :
    (∑j ∈ Finset.Ico (p+1) (⌊α*(n:ℝ)⌋₊+1), a j) ≤
      B*(2*(D*((p:ℝ)+1))^(p+1)/(n:ℝ)^(p+1)) := by
  calc
    _ ≤ ∑j ∈ Finset.Ico (p+1) (⌊α*(n:ℝ)⌋₊+1), B*term D n j :=
      Finset.sum_le_sum ha
    _ = B*(∑j ∈ Finset.Ico (p+1) (⌊α*(n:ℝ)⌋₊+1), term D n j) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_floor_window hD hα hαD n p hn) hB

end ActivityFiniteWindowBound

#print axioms ActivityFiniteWindowBound.sum_floor_window
#print axioms ActivityFiniteWindowBound.dominated_floor_window
