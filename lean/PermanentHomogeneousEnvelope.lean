import PermanentSpectralBound
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.Exponential

/-!
Finite exceptional-coordinate bounds for the actual homogeneous polynomial defined
in `PermanentEnergyIntegral`. The projection below forgets one exponent only after
using the fixed total degree to prove injectivity. No generating-function or circle
bound is assumed.
-/
noncomputable section
namespace PermanentPositiveMoments

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma homogeneous_mul_left (s : I → ℝ) (L : ℝ) (m : ℕ) :
    homogeneous (fun i => L * s i) m = L ^ m * homogeneous s m := by
  unfold homogeneous
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, (Finset.mem_piAntidiag.mp hk).1]

/-- A selected coordinate can reach one; all other coordinates are summed by
finite geometric sums. The degree may be zero and the complement may be empty. -/
theorem homogeneous_le_geometric_product (r : I → ℝ) (m : ℕ) (i0 : I)
    (hr0 : ∀ i, 0 ≤ r i) (htop : r i0 ≤ 1)
    (hrest : ∀ i, i ≠ i0 → r i < 1) :
    homogeneous r m ≤ ∏ i ∈ Finset.univ.erase i0, (1 - r i)⁻¹ := by
  classical
  let P := Finset.piAntidiag (Finset.univ : Finset I) m
  let e : (I → ℕ) → (I → ℕ) := fun k => Function.update k i0 0
  let t : I → Finset ℕ := fun i =>
    if i = i0 then {0} else Finset.range (m + 1)
  let T := Fintype.piFinset t
  have hinj : Set.InjOn e P := by
    intro k hk l hl he
    have hsame : ∀ i, i ≠ i0 → k i = l i := by
      intro i hi
      simpa only [e, Function.update_of_ne hi] using congrFun he i
    have hs : (∑ i ∈ Finset.univ.erase i0, k i) =
        ∑ i ∈ Finset.univ.erase i0, l i :=
      Finset.sum_congr rfl (fun i hi => hsame i (Finset.mem_erase.mp hi).1)
    have hkdeg := (Finset.mem_piAntidiag.mp hk).1
    have hldeg := (Finset.mem_piAntidiag.mp hl).1
    rw [← Finset.sum_erase_add Finset.univ k (Finset.mem_univ i0)] at hkdeg
    rw [← Finset.sum_erase_add Finset.univ l (Finset.mem_univ i0)] at hldeg
    funext i
    by_cases hi : i = i0
    · subst i
      omega
    · exact hsame i hi
  have hsub : P.image e ⊆ T := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨l, hl, rfl⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    by_cases hi : i = i0
    · subst i
      simp [e, t]
    · have hli : l i ≤ m := by
        calc
          l i ≤ ∑ j, l j := Finset.single_le_sum
            (fun j _ => Nat.zero_le (l j)) (Finset.mem_univ i)
          _ = m := (Finset.mem_piAntidiag.mp hl).1
      simpa only [e, t, hi, if_false, Function.update_of_ne hi,
        Finset.mem_range] using Nat.lt_succ_of_le hli
  have hsum : homogeneous r m ≤ ∑ k ∈ T, ∏ i, r i ^ k i := by
    change (∑ k ∈ P, ∏ i, r i ^ k i) ≤ _
    refine Finset.sum_le_sum_of_injOn e hinj hsub ?_ ?_
    · intro k hk
      apply Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hr0 i) _)
      intro i hi
      by_cases h : i = i0
      · subst i
        simpa only [e, Function.update_self, pow_zero] using
          (pow_le_one₀ (hr0 i0) htop : r i0 ^ k i0 ≤ 1)
      · simp only [e, Function.update_of_ne h, le_refl]
    · intro k hk hmissing
      exact Finset.prod_nonneg (fun i _ => pow_nonneg (hr0 i) _)
  calc
    homogeneous r m ≤ ∑ k ∈ T, ∏ i, r i ^ k i := hsum
    _ = ∏ i, ∑ j ∈ t i, r i ^ j :=
      (Finset.prod_univ_sum t (fun i j => r i ^ j)).symm
    _ = ∏ i ∈ Finset.univ.erase i0,
        ∑ j ∈ Finset.range (m + 1), r i ^ j := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => ∑ j ∈ t i, r i ^ j) (Finset.mem_univ i0)]
      simp only [t, if_pos rfl, Finset.sum_singleton, pow_zero, one_mul]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [(Finset.mem_erase.mp hi).1, if_false]
    _ ≤ ∏ i ∈ Finset.univ.erase i0, (1 - r i)⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg (fun j _ => pow_nonneg (hr0 i) _)
      · intro i hi
        simpa only [Nat.Ico_zero_eq_range, pow_zero, one_div] using
          (geom_sum_Ico_le_of_lt_one (m := 0) (n := m + 1) (hr0 i)
            (hrest i (Finset.mem_erase.mp hi).1))

/-- Rescaling only requires `L > 0` and strict separation of the other roots
from `L`; it does not require an ordering of the indices. -/
theorem homogeneous_le_rescaled_product (s : I → ℝ) (m : ℕ) (i0 : I)
    {L : ℝ} (hL : 0 < L) (hs0 : ∀ i, 0 ≤ s i) (htop : s i0 ≤ L)
    (hrest : ∀ i, i ≠ i0 → s i < L) :
    homogeneous s m ≤ L ^ m *
      ∏ i ∈ Finset.univ.erase i0, (1 - s i / L)⁻¹ := by
  have hscale : homogeneous s m =
      L ^ m * homogeneous (fun i => s i / L) m := by
    simpa only [mul_div_cancel₀ _ hL.ne'] using
      homogeneous_mul_left (fun i => s i / L) L m
  rw [hscale]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hL.le _)
  apply homogeneous_le_geometric_product
  · intro i
    exact div_nonneg (hs0 i) hL.le
  · exact (div_le_one₀ hL).mpr htop
  · intro i hi
    exact (div_lt_one hL).mpr (hrest i hi)

/-- The requested geometric product bound under a uniform nonexceptional
root bound `q < 1`. The hypotheses remain meaningful for an empty complement. -/
theorem homogeneous_exceptional_product_bound (s : I → ℝ) (m : ℕ) (i0 : I)
    {L q : ℝ} (hL : 1 ≤ L) (hs0 : ∀ i, 0 ≤ s i) (htop : s i0 ≤ L)
    (hrest : ∀ i, i ≠ i0 → s i ≤ q) (hq : q < 1) :
    homogeneous s m ≤ L ^ m *
      ∏ i ∈ Finset.univ.erase i0, (1 - s i / L)⁻¹ := by
  apply homogeneous_le_rescaled_product s m i0
    (lt_of_lt_of_le zero_lt_one hL) hs0 htop
  intro i hi
  exact (hrest i hi).trans_lt (hq.trans_le hL)

private lemma geometric_factor_le_one_add {x L q : ℝ}
    (hx : 0 ≤ x) (hL : 1 ≤ L) (hxq : x ≤ q) (hq : q < 1) :
    (1 - x / L)⁻¹ ≤ 1 + x / (1 - q) := by
  have hrs : x / L ≤ x := div_le_self hx hL
  have hrq : x / L ≤ q := hrs.trans hxq
  have hden : 0 < 1 - x / L := sub_pos.mpr (hrq.trans_lt hq)
  have hqden : 0 < 1 - q := sub_pos.mpr hq
  have hratio : (x / L) / (1 - x / L) ≤ x / (1 - q) :=
    div_le_div₀ hx hrs hqden (sub_le_sub_left hrq 1)
  have hid : (1 - x / L)⁻¹ = 1 + (x / L) / (1 - x / L) := by
    calc
      (1 - x / L)⁻¹ = ((1 - x / L) + x / L) / (1 - x / L) := by
        rw [sub_add_cancel, one_div]
      _ = (1 - x / L) / (1 - x / L) + (x / L) / (1 - x / L) :=
        add_div _ _ _
      _ = 1 + (x / L) / (1 - x / L) := by rw [div_self hden.ne']
  rw [hid]
  exact add_le_add le_rfl hratio

/-- An elementary product-to-exponential bound, with no logarithm or infinite
geometric series. No nonnegativity assumption on `q` is necessary. -/
theorem exceptional_product_le_exp (s : I → ℝ) (i0 : I)
    {L q : ℝ} (hL : 1 ≤ L) (hs0 : ∀ i, 0 ≤ s i)
    (hrest : ∀ i, i ≠ i0 → s i ≤ q) (hq : q < 1) :
    (∏ i ∈ Finset.univ.erase i0, (1 - s i / L)⁻¹) ≤
      Real.exp ((∑ i ∈ Finset.univ.erase i0, s i) / (1 - q)) := by
  have hqden : 0 < 1 - q := sub_pos.mpr hq
  calc
    (∏ i ∈ Finset.univ.erase i0, (1 - s i / L)⁻¹) ≤
        ∏ i ∈ Finset.univ.erase i0, (1 + s i / (1 - q)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        apply inv_nonneg.mpr
        have hrq : s i / L ≤ q :=
          (div_le_self (hs0 i) hL).trans (hrest i (Finset.mem_erase.mp hi).1)
        exact (sub_pos.mpr (hrq.trans_lt hq)).le
      · intro i hi
        exact geometric_factor_le_one_add (hs0 i) hL
          (hrest i (Finset.mem_erase.mp hi).1) hq
    _ ≤ Real.exp (∑ i ∈ Finset.univ.erase i0, s i / (1 - q)) :=
      Real.prod_one_add_le_exp_sum (Finset.univ.erase i0)
        (fun i => div_nonneg (hs0 i) hqden.le)
    _ = Real.exp ((∑ i ∈ Finset.univ.erase i0, s i) / (1 - q)) := by
      rw [Finset.sum_div]

/-- Finite homogeneous envelope at an arbitrary selected exceptional index. -/
theorem homogeneous_exceptional_exp_bound (s : I → ℝ) (m : ℕ) (i0 : I)
    {L q : ℝ} (hL : 1 ≤ L) (hs0 : ∀ i, 0 ≤ s i) (htop : s i0 ≤ L)
    (hrest : ∀ i, i ≠ i0 → s i ≤ q) (hq : q < 1) :
    homogeneous s m ≤ L ^ m *
      Real.exp ((∑ i ∈ Finset.univ.erase i0, s i) / (1 - q)) := by
  exact (homogeneous_exceptional_product_bound s m i0 hL hs0 htop hrest hq).trans
    (mul_le_mul_of_nonneg_left (exceptional_product_le_exp s i0 hL hs0 hrest hq)
      (pow_nonneg (zero_le_one.trans hL) _))

/-- The homogeneous estimate applies to the actual permanent through the proved
positive-moment spectral inequality. Spectral root bounds are explicit inputs. -/
theorem spectral_permanent_exceptional_exp_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (i0 : Fin n) {L q : ℝ}
    (hL : 1 ≤ L) (htop : PermanentSpectralFrame.singularRoot A i0 ≤ L)
    (hrest : ∀ i, i ≠ i0 → PermanentSpectralFrame.singularRoot A i ≤ q)
    (hq : q < 1) :
    ‖Matrix.permanent A‖ ≤ (n.factorial : ℝ) / (n : ℝ) ^ n * L ^ n *
      Real.exp ((∑ i ∈ Finset.univ.erase i0,
        PermanentSpectralFrame.singularRoot A i) / (1 - q)) := by
  have hs0 : ∀ i, 0 ≤ PermanentSpectralFrame.singularRoot A i :=
    fun i => Real.sqrt_nonneg _
  have hh := homogeneous_exceptional_exp_bound
    (PermanentSpectralFrame.singularRoot A) n i0 hL hs0 htop hrest hq
  have hc : 0 ≤ (n.factorial : ℝ) / (n : ℝ) ^ n :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  exact (spectral_permanent_bound hn A).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hc)

end PermanentPositiveMoments

#print axioms PermanentPositiveMoments.homogeneous_le_geometric_product
#print axioms PermanentPositiveMoments.homogeneous_exceptional_exp_bound
#print axioms PermanentPositiveMoments.spectral_permanent_exceptional_exp_bound
