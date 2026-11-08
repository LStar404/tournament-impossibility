import VectorWeakMajorization
noncomputable section
namespace TransitiveOrbit
open Finset Matrix

def T (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i < j then 1 else if j < i then -1 else 0

lemma T_skew (n : ℕ) (i j : Fin n) : T n i j = -T n j i := by
  unfold T
  split_ifs <;> norm_num <;> omega

/-- The reference matrix is itself an actual tournament, including n=0. -/
def transitiveTournament (n : ℕ) : VectorWeakMajorization.Tournament n where
  entry := T n
  skew := T_skew n
  unit i j hij := by
    unfold T
    split_ifs <;> simp_all <;> omega

def epsilon (m : ℕ) (i : Fin (m+1)) : ℝ := if i = Fin.last m then -1 else 1
lemma epsilon_sq (m : ℕ) (i : Fin (m+1)) : epsilon m i * epsilon m i = 1 := by
  unfold epsilon; split_ifs <;> norm_num
lemma epsilon_pow (m : ℕ) (i : Fin (m+1)) : (epsilon m i)^2 = 1 := by
  simpa [pow_two] using epsilon_sq m i

def Covariant (m : ℕ) (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) : Prop :=
  ∀ i j, A (finRotate (m+1) i) (finRotate (m+1) j) = epsilon m i * epsilon m j * A i j

/-- The exact signed cyclic symmetry of the transitive matrix. -/
theorem T_covariant (m : ℕ) : Covariant m (T (m+1)) := by
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  have hpi := coe_finRotate i
  have hpj := coe_finRotate j
  unfold T epsilon
  simp only [Fin.lt_def]
  split_ifs <;> simp_all only [Fin.ext_iff, Fin.val_last, Fin.val_zero] <;> norm_num at * <;> omega

/-- Negative cyclic shift: column j is epsilon(j) times e_(rotate j). -/
def J (m : ℕ) : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
  fun i j => if i = finRotate (m+1) j then epsilon m j else 0

lemma mul_J (m : ℕ) (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (i j : Fin (m+1)) :
    (A * J m) i j = A i (finRotate (m+1) j) * epsilon m j := by
  simp [Matrix.mul_apply, J, mul_ite]

lemma J_mul (m : ℕ) (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) (i j : Fin (m+1)) :
    (J m * A) (finRotate (m+1) i) j = epsilon m i * A i j := by
  simp [Matrix.mul_apply, J, ite_mul]

/-- The transitive matrix commutes with the actual signed cyclic-shift matrix. -/
theorem T_commutes_J (m : ℕ) : T (m+1) * J m = J m * T (m+1) := by
  ext i j
  obtain ⟨a, rfl⟩ := (finRotate (m+1)).surjective i
  rw [mul_J, J_mul, T_covariant m a j]
  calc
    _ = epsilon m a * (epsilon m j * epsilon m j) * T (m+1) a j := by ring
    _ = _ := by rw [epsilon_sq]; ring

lemma identity_covariant (m : ℕ) : Covariant m (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℝ) := by
  intro i j
  by_cases hij : i = j
  · subst j; simp [epsilon_sq]
  · have hne : finRotate (m+1) i ≠ finRotate (m+1) j := fun h => hij ((finRotate _).injective h)
    simp [Matrix.one_apply, hij, hne]

lemma mul_covariant (m : ℕ) (A C : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (ha : Covariant m A) (hc : Covariant m C) : Covariant m (A*C) := by
  intro i j
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp (finRotate (m+1)) (fun k => A (finRotate (m+1) i) k * C k (finRotate (m+1) j))]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [ha i k, hc k j]
  calc
    _ = epsilon m i * epsilon m j * (epsilon m k * epsilon m k) * (A i k * C k j) := by ring
    _ = _ := by rw [epsilon_sq]; ring

theorem power_covariant (m r : ℕ) : Covariant m ((T (m+1))^r) := by
  induction r with
  | zero => simpa using identity_covariant m
  | succ r ih =>
    rw [pow_succ]
    exact mul_covariant m _ _ ih (T_covariant m)

def columnSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  ∑ i, (A i j)^2

lemma columnSq_rotate (m : ℕ) (A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ)
    (ha : Covariant m A) (j : Fin (m+1)) :
    columnSq A (finRotate (m+1) j) = columnSq A j := by
  unfold columnSq
  rw [← Equiv.sum_comp (finRotate (m+1)) (fun i => (A i (finRotate (m+1) j))^2)]
  apply sum_congr rfl
  intro i hi
  rw [ha i j, mul_pow, mul_pow, epsilon_pow, epsilon_pow]
  ring

/-- All columns of every nonnegative integer power have the same squared norm. -/
theorem power_columns_equal (m r : ℕ) (j : Fin (m+1)) :
    columnSq ((T (m+1))^r) j = columnSq ((T (m+1))^r) 0 := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    have h := columnSq_rotate m ((T (m+1))^r) (power_covariant m r) j.castSucc
    have hr : finRotate (m+1) j.castSucc = j.succ := by
      simpa using finRotate_of_lt j.isLt
    rw [hr] at h
    exact h.trans ih

/-- Dimension-uniform version; the empty dimension is covered vacuously. -/
theorem power_columns_eq (n r : ℕ) (i j : Fin n) :
    columnSq ((T n)^r) i = columnSq ((T n)^r) j := by
  cases n with
  | zero => exact i.elim0
  | succ m => exact (power_columns_equal m r i).trans (power_columns_equal m r j).symm


/-- Finite Frobenius-square reduction to the reference column. -/
theorem power_frobenius (m r : ℕ) :
    (∑ i : Fin (m+1), ∑ j : Fin (m+1), (((T (m+1))^r) i j)^2) =
      ((m+1 : ℕ) : ℝ) * columnSq ((T (m+1))^r) 0 := by
  rw [sum_comm]
  change (∑ j : Fin (m+1), columnSq ((T (m+1))^r) j) = _
  simp_rw [power_columns_equal m r]
  simp

end TransitiveOrbit
#print axioms TransitiveOrbit.T_covariant
#print axioms TransitiveOrbit.power_columns_equal

#print axioms TransitiveOrbit.T_commutes_J

#print axioms TransitiveOrbit.power_columns_eq

#print axioms TransitiveOrbit.power_frobenius
