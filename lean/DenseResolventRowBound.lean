import RawBlockNeumannInverse
import RawResolventMeanBound

/-!
Focused compiled candidate. A Euclidean spectral gap and entry density imply dimension-free
row-absolute-sum bounds for the genuine resolvent. Infinity operator norms below
are on ordinary function spaces, never the EuclideanSpace used for the input.
-/
noncomputable section
namespace DenseResolventRowBound
open Matrix WithLp Finset
variable {m : ℕ}
abbrev Block (m : ℕ) := Fin m ⊕ Fin m

def resolvent (Q : Matrix (Block m) (Block m) ℂ) := (1 + Q)⁻¹

def entryConstant (C q : ℝ) : ℝ := C + 2 * C^2 / (1-q)
def rowConstant (C q : ℝ) : ℝ := 1 + 2 * entryConstant C q

lemma entryConstant_nonneg {C q : ℝ} (hC : 0 ≤ C) (hq : q < 1) :
    0 ≤ entryConstant C q := by
  have hp : 0 < 1-q := sub_pos.mpr hq
  unfold entryConstant
  positivity

/-- Genuine inverse existence and its Euclidean norm follow from the gap. -/
theorem inverse_data (Q : Matrix (Block m) (Block m) ℂ) {q : ℝ}
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q‖ ≤ q) (hq : q < 1) :
    resolvent Q * (1+Q) = 1 ∧ (1+Q) * resolvent Q = 1 ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (resolvent Q)‖ ≤ 1/(1-q) := by
  have h := RawBlockNeumannInverse.inverse_bound Q (1 : ℂ)
    (s := 1) (q := q) (by simp) hQ (by simpa using hq)
  have hu : IsUnit (1+Q) := by simpa using h.1
  have hd := (Matrix.isUnit_iff_isUnit_det (1+Q)).mp hu
  exact ⟨Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd, by
    simpa [resolvent] using h.2⟩

/-- The existing sandwich estimate replaces a new entrywise Neumann-series proof. -/
theorem inverse_entry_bound (hm : 0 < m) (Q : Matrix (Block m) (Block m) ℂ)
    {C q : ℝ} (hC : 0 ≤ C)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q‖ ≤ q) (hq : q < 1)
    (he : ∀ i j, ‖Q i j‖ ≤ C/(m : ℝ)) (i j : Block m) :
    ‖(resolvent Q - 1) i j‖ ≤ entryConstant C q / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : (Fintype.card (Block m) : ℝ) = 2*(m : ℝ) := by simp [Block]; ring
  have hu (i : Block m) :
      ‖toLp 2 (fun a => Q i a)‖ ≤ Real.sqrt (2*(m : ℝ)) * (C/(m : ℝ)) := by
    simpa only [hc] using RawResolventMeanBound.vector_bound (fun a => Q i a)
      (div_nonneg hC hmR.le) (he i)
  have hv (j : Block m) :
      ‖toLp 2 (fun a => Q a j)‖ ≤ Real.sqrt (2*(m : ℝ)) * (C/(m : ℝ)) := by
    simpa only [hc] using RawResolventMeanBound.vector_bound (fun a => Q a j)
      (div_nonneg hC hmR.le) (fun i => he i j)
  have hd := inverse_data Q hQ hq
  have h := RawResolventEntryBound.entry Q (resolvent Q) (1 : ℂ)
    (by simpa using hd.1) i j (s := 1) (by simp) (he i j) (hu i) (hv j) hd.2.2
  have hr : resolvent Q - 1 = -(Q * resolvent Q) := by
    calc
      _ = resolvent Q - (1+Q) * resolvent Q := by rw [hd.2.1]
      _ = _ := by rw [add_mul, one_mul]; abel
  rw [hr, Matrix.neg_apply, norm_neg]
  calc
    _ ≤ C/(m : ℝ) + (Real.sqrt (2*(m : ℝ)) * (C/(m : ℝ)))^2 * (1/(1-q)) := by
      simpa using h
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2*(m : ℝ))]
      unfold entryConstant
      field_simp [hmR.ne', sub_ne_zero.mpr (ne_of_lt hq).symm]

/-- The row sums, not a dimension-dependent conversion from the Euclidean norm. -/
theorem inverse_row_bound (hm : 0 < m) (Q : Matrix (Block m) (Block m) ℂ)
    {C q : ℝ} (hC : 0 ≤ C)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q‖ ≤ q) (hq : q < 1)
    (he : ∀ i j, ‖Q i j‖ ≤ C/(m : ℝ)) (i : Block m) :
    (∑ j, ‖resolvent Q i j‖) ≤ rowConstant C q := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hentry (j : Block m) :
      ‖resolvent Q i j‖ ≤ ‖(1 : Matrix (Block m) (Block m) ℂ) i j‖ +
        entryConstant C q/(m : ℝ) := by
    have hid : resolvent Q = 1 + (resolvent Q-1) := by abel
    calc
      _ = ‖(1 : Matrix (Block m) (Block m) ℂ) i j + (resolvent Q-1) i j‖ := by
        conv_lhs => rw [hid]
        rfl
      _ ≤ _ := (norm_add_le _ _).trans
        (add_le_add le_rfl (inverse_entry_bound hm Q hC hQ hq he i j))
  calc
    _ ≤ ∑ j, (‖(1 : Matrix (Block m) (Block m) ℂ) i j‖ +
        entryConstant C q/(m : ℝ)) := sum_le_sum (fun j _ => hentry j)
    _ = _ := by
      have hs : (∑ j, ‖(1 : Matrix (Block m) (Block m) ℂ) i j‖) = 1 := by
        rcases i with i | i <;> simp [Matrix.one_apply, apply_ite norm, eq_comm]
      rw [sum_add_distrib, hs]
      simp only [sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
      unfold rowConstant
      push_cast
      field_simp [hmR.ne']
      ring

section Infinity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ordinary Pi functions carry the supremum norm, unlike EuclideanSpace. -/
def infinityMap (A : Matrix ι ι ℂ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  ContinuousLinearMap.mk (Matrix.mulVecLin A)

@[simp] lemma infinityMap_apply (A : Matrix ι ι ℂ) (x : ι → ℂ) :
    infinityMap A x = A *ᵥ x := rfl

@[simp] lemma infinityMap_one : infinityMap (1 : Matrix ι ι ℂ) = 1 := by
  ext x i
  simp [infinityMap]

@[simp] lemma infinityMap_add (A B : Matrix ι ι ℂ) :
    infinityMap (A+B) = infinityMap A + infinityMap B := by
  ext x i
  change ((A+B) *ᵥ x) i = (A *ᵥ x) i + (B *ᵥ x) i
  rw [Matrix.add_mulVec]; rfl

@[simp] lemma infinityMap_mul (A B : Matrix ι ι ℂ) :
    infinityMap (A*B) = infinityMap A * infinityMap B := by
  ext x i
  change ((A*B) *ᵥ x) i = (A *ᵥ (B *ᵥ x)) i
  rw [Matrix.mulVec_mulVec]

/-- Explicit row sums give the infinity operator bound without changing instances. -/
theorem infinityMap_norm_le (A : Matrix ι ι ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ i, (∑ j, ‖A i j‖) ≤ K) : ‖infinityMap A‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg x))).mpr
  intro i
  change ‖∑ j, A i j * x j‖ ≤ K * ‖x‖
  calc
    _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
    _ = ∑ j, ‖A i j‖ * ‖x j‖ := by simp only [norm_mul]
    _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _))
    _ = (∑ j, ‖A i j‖) * ‖x‖ := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg x)
end Infinity

/-- The two norms are displayed as different continuous-linear-map types. -/
theorem inverse_infinity_bound (hm : 0 < m) (Q : Matrix (Block m) (Block m) ℂ)
    {C q : ℝ} (hC : 0 ≤ C)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q‖ ≤ q) (hq : q < 1)
    (he : ∀ i j, ‖Q i j‖ ≤ C/(m : ℝ)) :
    ‖infinityMap (resolvent Q)‖ ≤ rowConstant C q := by
  have hD := entryConstant_nonneg hC hq
  apply infinityMap_norm_le _ (by unfold rowConstant; positivity)
  exact inverse_row_bound hm Q hC hQ hq he

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
def neumann (A : E →L[ℂ] E) : E →L[ℂ] E := ∑' k : ℕ, (-A)^k

/-- This Banach-algebra lemma applies to the infinity-norm function space too. -/
theorem neumann_data (A : E →L[ℂ] E) {t : ℝ} (hA : ‖A‖ ≤ t) (ht : t < 1) :
    (1+A) * neumann A = 1 ∧ neumann A * (1+A) = 1 ∧
      ‖neumann A‖ ≤ 1/(1-t) := by
  have ha : ‖-A‖ < 1 := by simpa using hA.trans_lt ht
  refine ⟨?_, ?_, ?_⟩
  · simpa [neumann, sub_neg_eq_add] using mul_neg_geom_series (-A) ha
  · simpa [neumann, sub_neg_eq_add] using geom_series_mul_neg (-A) ha
  · have h := tsum_geometric_le_of_norm_lt_one (-A) ha
    have h1 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hinv : (1-‖-A‖)⁻¹ ≤ (1-t)⁻¹ :=
      inv_anti₀ (sub_pos.mpr ht) (by simpa using sub_le_sub_left hA 1)
    change ‖∑' k : ℕ, (-A)^k‖ ≤ _
    rw [one_div]
    linarith
end Banach
end DenseResolventRowBound
#print axioms DenseResolventRowBound.inverse_entry_bound
#print axioms DenseResolventRowBound.inverse_row_bound
#print axioms DenseResolventRowBound.inverse_infinity_bound
#print axioms DenseResolventRowBound.neumann_data
