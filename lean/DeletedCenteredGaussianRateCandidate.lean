import ActualDeletedCenteredGaussianCandidate

/-! Isolated finite-error rate reduction. No scaling or recovery theorem.
The scalar estimate uses only n≥24, m≥n/2, n=m+t and 0≤tau≤n.
The actual endpoint derives the tau cap from tournament marginals. -/
set_option autoImplicit false
noncomputable section
namespace DeletedCenteredGaussianRateCandidate
open Matrix Finset
open TournamentHamiltonian ActualTournamentPrescalingBounds TournamentPrescalingMassBound
open IndependentCenteringEnergyCandidate RealProjectionAggregationCandidate
open ActualTwoSidedCenteringCandidate ActualDeletedCenteredGaussianCandidate
open scoped Matrix.Norms.L2Operator BigOperators

def gap : ℝ := 205/529

def finiteError (n m t τ : ℝ) : ℝ :=
  19/n+(t*(n+m)/(n-1)^2)/(2*gap)+
    (4*τ+4*n/(n-1)^2+4*m*t^2/(n-1)^2)/(2*m*gap)

lemma gap_eq : gap = 1-(18/23:ℝ)^2 := by norm_num [gap]
lemma gap_pos : 0 < gap := by norm_num [gap]

lemma finiteError_split (n m t τ : ℝ) (hn : 0 < n) (hm : 0 < m) (hn1 : n ≠ 1) :
    finiteError n m t τ =
      19/n+(t*(n+m)*(1/(n-1)^2))/(2*gap)+
      (2*τ*(1/m))/gap+(2*n*(1/(n-1)^2)*(1/m))/gap+
      (2*t^2*(1/(n-1)^2))/gap := by
  unfold finiteError
  field_simp [hn.ne', hm.ne', sub_ne_zero.mpr hn1, gap_pos.ne']
  ring

theorem finiteError_le_coarse (n m t τ : ℝ) (hn : 24 ≤ n)
    (hm : n/2 ≤ m) (hcard : n = m+t) (ht : 0 ≤ t) (hτ : 0 ≤ τ) :
    finiteError n m t τ ≤
      19/n+4*t/(gap*n)+4*τ/(gap*n)+16/(gap*n^2)+8*t^2/(gap*n^2) := by
  have hn0 : 0 < n := by linarith
  have hm0 : 0 < m := by linarith
  have hd0 : 0 < n-1 := by linarith
  have hsum : n+m ≤ 2*n := by linarith
  have hden : 1/(n-1)^2 ≤ 4/n^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (sq_pos_of_pos hn0)).mpr
    nlinarith
  have hminv : 1/m ≤ 2/n := by
    apply (div_le_div_iff₀ hm0 hn0).mpr
    linarith
  rw [finiteError_split n m t τ hn0 hm0 (by linarith)]
  calc
    _ ≤ 19/n+(t*(2*n)*(4/n^2))/(2*gap)+
        (2*τ*(2/n))/gap+(2*n*(4/n^2)*(2/n))/gap+
        (2*t^2*(4/n^2))/gap := by
      gcongr <;> norm_num [gap]
    _ = _ := by
      field_simp [hn0.ne', gap_pos.ne']
      ring

theorem coarse_le_rate (n t τ : ℝ) (hn : 24 ≤ n)
    (ht0 : 0 ≤ t) (ht : t ≤ n/2) (_hτ0 : 0 ≤ τ) (hτ : τ ≤ n) :
    19/n+4*t/(gap*n)+4*τ/(gap*n)+16/(gap*n^2)+8*t^2/(gap*n^2) ≤
      64*(Real.sqrt (τ/n)+(t+1)/n) := by
  have hn0 : 0 < n := by linarith
  have htq0 : 0 ≤ t/n := div_nonneg ht0 hn0.le
  have htq : t/n ≤ 1/2 := (div_le_iff₀ hn0).mpr (by linarith)
  have hτq : τ/n ≤ 1 := (div_le_one hn0).mpr hτ
  have hsqrt : τ/n ≤ Real.sqrt (τ/n) := Real.le_sqrt_self_iff.mpr hτq
  have hinv : 1/n^2 ≤ 1/n := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hn0) hn0).mpr
    nlinarith
  have hsq : (t/n)^2 ≤ (t/n)/2 := by
    nlinarith [mul_nonneg htq0 (sub_nonneg.mpr htq)]
  calc
    _ = 19/n+(4/gap)*(t/n)+(4/gap)*(τ/n)+
        (16/gap)*(1/n^2)+(8/gap)*(t/n)^2 := by
      field_simp [hn0.ne', gap_pos.ne']
    _ ≤ 19/n+(4/gap)*(t/n)+(4/gap)*Real.sqrt (τ/n)+
        (16/gap)*(1/n)+(8/gap)*((t/n)/2) := by
      gcongr <;> norm_num [gap]
    _ = (19+16/gap)/n+(8/gap)*(t/n)+(4/gap)*Real.sqrt (τ/n) := by ring
    _ ≤ 64/n+64*(t/n)+64*Real.sqrt (τ/n) := by
      gcongr <;> norm_num [gap]
    _ = _ := by ring

theorem finiteError_le_rate (n m t τ : ℝ) (hn : 24 ≤ n)
    (hm : n/2 ≤ m) (hcard : n = m+t) (ht : 0 ≤ t) (hτ0 : 0 ≤ τ) (hτ : τ ≤ n) :
    finiteError n m t τ ≤ 64*(Real.sqrt (τ/n)+(t+1)/n) :=
  (finiteError_le_coarse n m t τ hn hm hcard ht hτ0).trans
    (coarse_le_rate n t τ hn ht (by linarith) hτ0 hτ)

lemma normalizedScore_abs_le_one {n : ℕ} (T : Tournament n) (hn : 2 ≤ n) (i : Fin n) :
    |normalizedScore T i| ≤ 1 := by
  have hr : 0 ≤ ∑ j, baseMatrix T i j := sum_nonneg (fun j _ => base_nonneg T hn i j)
  have hc : 0 ≤ ∑ j, baseMatrix T j i := sum_nonneg (fun j _ => base_nonneg T hn j i)
  rw [base_row T hn i] at hr
  rw [base_col T hn i] at hc
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem actual_tau_le_card {n : ℕ} (T : Tournament n) (hn : 2 ≤ n) :
    tau (normalizedScore T) ≤ (n:ℝ) := by
  calc
    _ ≤ ∑ _i : Fin n, (1:ℝ) := sum_le_sum (fun i _ =>
      (sq_le_one_iff_abs_le_one _).mpr (normalizedScore_abs_le_one T hn i))
    _ = _ := by simp

/-- Actual endpoint: the score-energy cap is proved, not assumed. Independent
deleted row/column sets need not agree. No extra operator gap or scaling input. -/
theorem actual_independent_centered_rate {n m : ℕ} (T : Tournament n)
    (hn : 24 ≤ n) (hhalf : (n:ℝ)/2 ≤ (m:ℝ))
    (I J : Finset (Fin n)) (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (t : ℕ) (hI : I.card = t) (hJ : J.card = t) :
    let Z := (realZ T).submatrix (retainedEmbedding I r) (retainedEmbedding J c)
    ‖g (center m*Z*center m)-g (SkewBaselineGramDifferenceCandidate.scaled (signMatrix T))‖ ≤
      64*(Real.sqrt (tau (normalizedScore T)/(n:ℝ))+((t:ℝ)+1)/(n:ℝ)) := by
  have hnR : (24:ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (0:ℝ) < m := by linarith
  have hm : 0 < m := by exact_mod_cast hmR
  have hcard : (n:ℝ) = (m:ℝ)+(t:ℝ) := by
    exact_mod_cast retained_card_relation I r t hI
  have hb := actual_independent_centered_total T hn hm I J r c t hI hJ
  rw [← gap_eq] at hb
  exact hb.trans (finiteError_le_rate (n:ℝ) (m:ℝ) (t:ℝ) (tau (normalizedScore T))
    hnR hhalf hcard (Nat.cast_nonneg _) (tau_nonneg _) (actual_tau_le_card T (by omega)))

end DeletedCenteredGaussianRateCandidate
