import TournamentHamiltonian.SkewSpectrum
import TournamentHamiltonian.PathConvolution

/-! The rank-one factor in the actual principal-minor generating determinant. -/
namespace TournamentHamiltonian
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem one_add_skew_quadratic (S : Matrix ι ι ℝ) (hS : ∀ i j, S i j = -S j i)
    (x : ι → ℝ) : dotProduct x (((1 : Matrix ι ι ℝ) + S).mulVec x) = ∑ i, x i ^ 2 := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, skew_quadratic_zero S hS, add_zero]
  simp only [dotProduct, pow_two]

theorem det_one_add_skew_pos (S : Matrix ι ι ℝ) (hS : ∀ i j, S i j = -S j i) :
    0 < ((1 : Matrix ι ι ℝ) + S).det := by
  apply det_pos_of_quadraticPositive
  intro x hx
  rw [one_add_skew_quadratic S hS]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem skew_inverse_quadratic_le (S : Matrix ι ι ℝ) (hS : ∀ i j, S i j = -S j i)
    (x : ι → ℝ) :
    dotProduct x (((1 : Matrix ι ι ℝ) + S)⁻¹.mulVec x) ≤ ∑ i, x i ^ 2 := by
  let M : Matrix ι ι ℝ := 1 + S
  let y := M⁻¹.mulVec x
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr (det_one_add_skew_pos S hS).ne'
  have hmy : M.mulVec y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu, Matrix.one_mulVec]
  have hdot : dotProduct y x = ∑ i, y i ^ 2 := by
    rw [← hmy, one_add_skew_quadratic S hS]
  have hsum : (∑ i, (x i - y i) ^ 2) = (∑ i, x i ^ 2) - ∑ i, y i ^ 2 := by
    calc
      _ = (∑ i, x i ^ 2) + (∑ i, y i ^ 2) - 2 * dotProduct y x := by
        simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hdot]; ring
  have hn := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) => sq_nonneg (x i - y i))
  rw [hsum] at hn
  change dotProduct x y ≤ _
  rw [dotProduct_comm, hdot]
  linarith

theorem det_one_add_skew_add_ones_le (S : Matrix ι ι ℝ) (hS : ∀ i j, S i j = -S j i)
    (c : ℝ) (hc : 0 ≤ c) :
    ((1 : Matrix ι ι ℝ) + S + c • Matrix.of (fun _ _ => (1 : ℝ))).det ≤
      ((1 : Matrix ι ι ℝ) + S).det * (1 + c * Fintype.card ι) := by
  let M : Matrix ι ι ℝ := 1 + S
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr (det_one_add_skew_pos S hS).ne'
  have hrank : c • Matrix.of (fun _ _ : ι => (1 : ℝ)) =
      Matrix.replicateCol Unit (fun _ : ι => c) * Matrix.replicateRow Unit (fun _ : ι => (1 : ℝ)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hrank, Matrix.det_add_replicateCol_mul_replicateRow hu]
  have heq : (Matrix.replicateRow Unit (fun _ : ι => (1 : ℝ)) * M⁻¹ *
      Matrix.replicateCol Unit (fun _ : ι => c)) default default =
      c * dotProduct (fun _ : ι => (1 : ℝ)) (M⁻¹.mulVec (fun _ : ι => (1 : ℝ))) := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Matrix.det_unique (n := Unit)]
  simp only [Matrix.add_apply, Matrix.one_apply_eq]
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (det_one_add_skew_pos S hS).le
  apply add_le_add (le_refl 1)
  apply mul_le_mul_of_nonneg_left _ hc
  simpa using skew_inverse_quadratic_le S hS (fun _ => 1)

theorem signMatrix_real_kernel_det {n : ℕ} (T : Tournament n) (z : ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + z • signMatrix T).det =
      ((positiveSkewFrequencies T).map (fun x : ℝ => 1 + z ^ 2 * x ^ 2)).prod := by
  apply Complex.ofReal_injective
  have hm := Complex.ofRealHom.map_det ((1 : Matrix (Fin n) (Fin n) ℝ) + z • signMatrix T)
  have heq : (((1 : Matrix (Fin n) (Fin n) ℝ) + z • signMatrix T).map Complex.ofRealHom) =
      (1 : Matrix (Fin n) (Fin n) ℂ) + (z : ℂ) • complexSignMatrix T := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, complexSignMatrix]
  change (((1 : Matrix (Fin n) (Fin n) ℝ) + z • signMatrix T).det : ℂ) =
    (((1 : Matrix (Fin n) (Fin n) ℝ) + z • signMatrix T).map Complex.ofRealHom).det at hm
  rw [heq, complexSignMatrix_kernel_det] at hm
  have hp := map_multiset_prod Complex.ofRealHom ((positiveSkewFrequencies T).map (fun x : ℝ => 1 + z ^ 2 * x ^ 2))
  simp only [Multiset.map_map, Function.comp_def, Complex.ofRealHom_eq_coe,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_one] at hp
  exact hm.trans hp.symm

theorem signMatrix_kernel_det_mono {n : ℕ} (T : Tournament n) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + a • signMatrix T).det ≤
      ((1 : Matrix (Fin n) (Fin n) ℝ) + b • signMatrix T).det := by
  rw [signMatrix_real_kernel_det, signMatrix_real_kernel_det]
  induction positiveSkewFrequencies T using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    apply mul_le_mul
    · nlinarith [mul_nonneg (show 0 ≤ b ^ 2 - a ^ 2 by nlinarith) (sq_nonneg x)]
    · exact ih
    · apply Multiset.prod_nonneg
      intro y hy
      obtain ⟨t, _, rfl⟩ := Multiset.mem_map.mp hy
      positivity
    · positivity


end TournamentHamiltonian

namespace TournamentHamiltonian
end TournamentHamiltonian
