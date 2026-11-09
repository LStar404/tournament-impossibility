import WeightedRecoveryMultiplier
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Finite-(j,a) recovery series and its weighted omitted
tail. This never forms an infinite sum over activities. -/
noncomputable section
namespace RecoveryMomentTail
open WeightedCoefficientNorm PermanentTruncatedRecoveryAlgebra
open ActualResidualFrozenFactorization BinaryGraphActivityBound

lemma H_nonneg (k a : ℕ) : 0≤RecoveryFiniteOrderRemainder.H k a :=
  RecoveryHomogeneousList.nonnegative _ (fun x hx => (RecoveryFiniteOrderRemainder.nodes_mem k x hx).1) a

lemma H_bound (k a : ℕ) : RecoveryFiniteOrderRemainder.H k a≤(k : ℝ)^(2*a) := by
  have h := RecoveryHomogeneousList.bound (RecoveryFiniteOrderRemainder.nodes k)
    (fun x hx => (RecoveryFiniteOrderRemainder.nodes_mem k x hx).1) a
  have hs : 0≤(RecoveryFiniteOrderRemainder.nodes k).sum :=
    List.sum_nonneg (fun x hx => (RecoveryFiniteOrderRemainder.nodes_mem k x hx).1)
  exact h.trans (by simpa only [pow_mul] using (pow_le_pow_left₀ hs (RecoveryFiniteOrderRemainder.nodes_sum_bound k) a))

lemma multiplier_nonneg (n q k : ℕ) : 0≤ multiplier n q k := by
  apply Finset.sum_nonneg
  intro a ha
  exact div_nonneg (H_nonneg k a) (pow_nonneg (Nat.cast_nonneg n) a)

lemma moment_window (F : PowerSeries ℂ) (E : Finset ℕ) (ell : ℕ)
    (hF : Finite (9/8) F) :
    (∑ k∈E, (k : ℝ)^ell*‖F.coeff k‖)≤
      WeightedPolynomialMultiplier.moment (8/9) ell*norm (9/8) F := by
  simpa only [one_pow, mul_one, show (1 : ℝ)/(9/8)=8/9 by norm_num] using
    WeightedPolynomialMultiplier.finite_window F E ell 1 (9/8) 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hF

lemma pair_tail (n a q ell : ℕ) (hn : 0<n) (alpha : ℝ) (halpha : 0<alpha)
    (F : PowerSeries ℂ) (hF : Finite (9/8) F) (E : Finset ℕ)
    (hE : ∀ k∈E, ⌊alpha*(n : ℝ)⌋₊<k) :
    (∑ k∈E, (RecoveryFiniteOrderRemainder.H k a/(n : ℝ)^a)*(k : ℝ)^ell*‖F.coeff k‖)≤
      (WeightedPolynomialMultiplier.moment (8/9) (2*a+ell+q)/
        ((n : ℝ)^a*(alpha*(n : ℝ))^q))*norm (9/8) F := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hd : 0<(n : ℝ)^a*(alpha*(n : ℝ))^q := by positivity
  have hp (k : ℕ) (hk : k∈E) :
      (RecoveryFiniteOrderRemainder.H k a/(n : ℝ)^a)*(k : ℝ)^ell≤
        (k : ℝ)^(2*a+ell+q)/((n : ℝ)^a*(alpha*(n : ℝ))^q) := by
    have hcut : alpha*(n : ℝ)≤k := (Nat.lt_of_floor_lt (hE k hk)).le
    have hpow := pow_le_pow_left₀ (by positivity : 0≤alpha*(n : ℝ)) hcut q
    have hpoly : RecoveryFiniteOrderRemainder.H k a*(k : ℝ)^ell*(alpha*(n : ℝ))^q≤
        (k : ℝ)^(2*a+ell+q) := by
      calc
        _ ≤ (k : ℝ)^(2*a)*(k : ℝ)^ell*(k : ℝ)^q :=
          mul_le_mul (mul_le_mul_of_nonneg_right (H_bound k a) (by positivity))
            hpow (by positivity) (by positivity)
        _ = _ := by rw [pow_add, pow_add]
    apply (le_div_iff₀ hd).mpr
    calc
      _ = RecoveryFiniteOrderRemainder.H k a*(k : ℝ)^ell*(alpha*(n : ℝ))^q := by
        field_simp
      _ ≤ _ := hpoly
  calc
    _ ≤ ∑ k∈E, ((k : ℝ)^(2*a+ell+q)/((n : ℝ)^a*(alpha*(n : ℝ))^q))*‖F.coeff k‖ :=
      Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right (hp k hk) (norm_nonneg _))
    _ = (1/((n : ℝ)^a*(alpha*(n : ℝ))^q))*(∑ k∈E, (k : ℝ)^(2*a+ell+q)*‖F.coeff k‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (1/((n : ℝ)^a*(alpha*(n : ℝ))^q))*
        (WeightedPolynomialMultiplier.moment (8/9) (2*a+ell+q)*norm (9/8) F) :=
      mul_le_mul_of_nonneg_left (moment_window F E _ hF) (by positivity)
    _ = _ := by ring

def untruncated {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (recoveredCoefficient M p)

lemma coefficient {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p k : ℕ) :
    (untruncated M p).coeff k=recoveredCoefficient M p k := PowerSeries.coeff_mk _ _

lemma coefficient_majorant {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p ell k : ℕ) :
    (k : ℝ)^ell*‖(untruncated M p).coeff k‖≤
      ∑ j∈Finset.range (p+1), ∑ a∈Finset.range (p-j+1),
        (RecoveryFiniteOrderRemainder.H k a/(n : ℝ)^a)*(k : ℝ)^ell*
          ‖(core M*rawActivity M j).coeff k‖ := by
  rw [coefficient]
  calc
    _ ≤ (k : ℝ)^ell*(∑ j∈Finset.range (p+1),
        ‖(multiplier n (p-j) k : ℂ)*(core M*rawActivity M j).coeff k‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (multiplier_nonneg n (p-j) k)]
      unfold multiplier
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

def tailConstant (alpha : ℝ) (L : ℕ → ℝ) (p ell : ℕ) : ℝ :=
  ∑ j∈Finset.range (p+1), ∑ a∈Finset.range (p-j+1),
    L j*WeightedPolynomialMultiplier.moment (8/9) (2*a+ell+(p+1-j-a))/alpha^(p+1-j-a)

/-- Only finitely many activities and recovery orders occur. The coefficient
tail is controlled for every finite subset, ready for a summability theorem. -/
theorem approximation_tail {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0<n) (p ell : ℕ) (alpha : ℝ) (halpha : 0<alpha) (L : ℕ → ℝ)
    (hF : ∀ j∈Finset.range (p+1), Finite (9/8) (core M*rawActivity M j))
    (bF : ∀ j∈Finset.range (p+1), norm (9/8) (core M*rawActivity M j)≤L j/(n : ℝ)^j)
    (E : Finset ℕ) (hE : ∀ k∈E, ⌊alpha*(n : ℝ)⌋₊<k) :
    (∑ k∈E, (k : ℝ)^ell*‖(untruncated M p).coeff k‖)≤
      tailConstant alpha L p ell/(n : ℝ)^(p+1) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  calc
    _ ≤ ∑ k∈E, ∑ j∈Finset.range (p+1), ∑ a∈Finset.range (p-j+1),
        (RecoveryFiniteOrderRemainder.H k a/(n : ℝ)^a)*(k : ℝ)^ell*
          ‖(core M*rawActivity M j).coeff k‖ :=
      Finset.sum_le_sum (fun k hk => coefficient_majorant M p ell k)
    _ = ∑ j∈Finset.range (p+1), ∑ a∈Finset.range (p-j+1), ∑ k∈E,
        (RecoveryFiniteOrderRemainder.H k a/(n : ℝ)^a)*(k : ℝ)^ell*
          ‖(core M*rawActivity M j).coeff k‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ ≤ ∑ j∈Finset.range (p+1), ∑ a∈Finset.range (p-j+1),
        (L j*WeightedPolynomialMultiplier.moment (8/9) (2*a+ell+(p+1-j-a))/alpha^(p+1-j-a))/(n : ℝ)^(p+1) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro a ha
      have hjp : j≤p := by simpa using hj
      have hap : a≤p-j := by simpa using ha
      have hexp : a+(p+1-j-a)+j=p+1 := by omega
      have hp := pair_tail n a (p+1-j-a) ell hn alpha halpha
        (core M*rawActivity M j) (hF j hj) E hE
      have hm : 0≤WeightedPolynomialMultiplier.moment (8/9) (2*a+ell+(p+1-j-a)) :=
        tsum_nonneg (fun k => by positivity)
      apply hp.trans
      calc
        _ ≤ (WeightedPolynomialMultiplier.moment (8/9) (2*a+ell+(p+1-j-a))/
            ((n : ℝ)^a*(alpha*(n : ℝ))^(p+1-j-a)))*(L j/(n : ℝ)^j) :=
          mul_le_mul_of_nonneg_left (bF j hj) (by positivity)
        _ = _ := by
          have hpows : (n : ℝ)^a*(n : ℝ)^(p+1-j-a)*(n : ℝ)^j=(n : ℝ)^(p+1) := by
            rw [← pow_add, ← pow_add, hexp]
          rw [div_mul_div_comm, mul_pow, div_div]
          congr 1
          · ring
          · calc
              _ = alpha^(p+1-j-a)*((n : ℝ)^a*(n : ℝ)^(p+1-j-a)*(n : ℝ)^j) := by ring
              _ = _ := by rw [hpows]
    _ = _ := by simp only [tailConstant, Finset.sum_div]
end RecoveryMomentTail
#print axioms RecoveryMomentTail.approximation_tail
