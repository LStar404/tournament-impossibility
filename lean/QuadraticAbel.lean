import Abel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Quadratic weights in Abel's limit theorem

The paper's third generating function is normalized by `(1-r)^3`, because its
coefficients differ from `L` only at order `n^{-2}`.  This file supplies the two
analytic ingredients:

* `abel_sq_tendsto_zero`: a coefficient sequence tending to zero has a vanishing
  quadratically weighted Abel mean of order three.
* `abel_sq_weight`: a coefficient sequence tending to `L` has quadratically
  weighted Abel mean tending to `2 L`.

Neither statement assumes monotonicity or a rate of convergence.  The development
is kept as a chain of small lemmas: one large declaration made elaboration
quadratic on this machine.
-/

open Filter Topology
open scoped BigOperators

namespace NonAlgebraicity

/-- The quadratically weighted summand `n^2 d n r^n`. -/
noncomputable def sqterm (d : ℕ → ℂ) (r : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ 2 * d n * r ^ n

theorem norm_sq_natCast (n : ℕ) : ‖((n : ℂ)) ^ 2‖ = ((n : ℝ)) ^ 2 := by
  have hpt : ((n : ℂ)) = (((n : ℝ)) : ℂ) := by push_cast; ring
  rw [norm_pow, hpt, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Quadratic weights are summable against a bounded coefficient sequence. -/
theorem summable_sq_mul_abel {d : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖d n‖ ≤ C)
    {r : ℝ} (hr : ‖(r : ℂ)‖ < 1) : Summable fun n : ℕ => sqterm d (r : ℂ) n := by
  have hg : Summable fun n : ℕ => C * ‖(n : ℂ) ^ 2 * (r : ℂ) ^ n‖ :=
    (summable_norm_pow_mul_geometric_of_norm_lt_one 2 hr).mul_left C
  refine hg.of_norm_bounded (fun n => ?_)
  have hdef : ‖sqterm d (r : ℂ) n‖ = ‖(n : ℂ) ^ 2‖ * ‖d n‖ * ‖(r : ℂ) ^ n‖ := by
    simp only [sqterm, norm_mul]
  rw [hdef]
  calc ‖(n : ℂ) ^ 2‖ * ‖d n‖ * ‖(r : ℂ) ^ n‖
      ≤ ‖(n : ℂ) ^ 2‖ * C * ‖(r : ℂ) ^ n‖ := by
        gcongr
        exact hC n
    _ = C * (‖(n : ℂ) ^ 2‖ * ‖(r : ℂ) ^ n‖) := by ring
    _ = C * ‖(n : ℂ) ^ 2 * (r : ℂ) ^ n‖ := by rw [norm_mul]

/-- Summability survives the index shift. -/
theorem shift_summable {d : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖d n‖ ≤ C) {N : ℕ}
    {r : ℝ} (hr : ‖(r : ℂ)‖ < 1) : Summable fun k : ℕ => sqterm d (r : ℂ) (k + N) := by
  have hsum : Summable fun n : ℕ => sqterm d (r : ℂ) n := summable_sq_mul_abel hC hr
  exact (summable_nat_add_iff N).mpr hsum

/-- The shifted real majorant is summable. -/
theorem target_summable {N : ℕ} {r : ℝ} (hrreal : ‖r‖ < 1) :
    Summable fun k : ℕ => ((k + N : ℕ) : ℝ) ^ 2 * r ^ (k + N) := by
  have hgs : Summable fun m : ℕ => (m : ℝ) ^ 2 * r ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hrreal
  exact (summable_nat_add_iff N).mpr hgs

/-- Pointwise comparison of a shifted summand with the majorant. -/
theorem pointwise_bound {d : ℕ → ℂ} {ε : ℝ} {N : ℕ} {r : ℝ} (hrpos : 0 < r)
    (hN : ∀ n, N ≤ n → ‖d n‖ ≤ ε / 8) :
    ∀ k : ℕ, ‖sqterm d (r : ℂ) (k + N)‖
      ≤ (ε / 8) * (((k + N : ℕ) : ℝ) ^ 2 * r ^ (k + N)) := by
  intro k
  have hdN : ‖d (k + N)‖ ≤ ε / 8 := hN (k + N) (by omega)
  have hrn : ‖(r : ℂ) ^ (k + N)‖ = r ^ (k + N) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have hdef : ‖sqterm d (r : ℂ) (k + N)‖
      = (((k + N : ℕ) : ℝ) ^ 2) * ‖d (k + N)‖ * r ^ (k + N) := by
    show ‖(((k + N : ℕ) : ℂ) ^ 2) * d (k + N) * (r : ℂ) ^ (k + N)‖ = _
    rw [norm_mul, norm_mul, hrn, norm_sq_natCast]
  rw [hdef]
  calc (((k + N : ℕ) : ℝ) ^ 2) * ‖d (k + N)‖ * r ^ (k + N)
      = ‖d (k + N)‖ * ((((k + N : ℕ) : ℝ) ^ 2) * r ^ (k + N)) := by ring
    _ ≤ (ε / 8) * ((((k + N : ℕ) : ℝ) ^ 2) * r ^ (k + N)) := by gcongr

/-- The norms of the shifted summands are summable. -/
theorem norm_summable {d : ℕ → ℂ} {ε : ℝ} {N : ℕ} {r : ℝ}
    (hgN : Summable fun k : ℕ => ((k + N : ℕ) : ℝ) ^ 2 * r ^ (k + N))
    (hterm : ∀ k : ℕ,
      ‖sqterm d (r : ℂ) (k + N)‖ ≤ (ε / 8) * (((k + N : ℕ) : ℝ) ^ 2 * r ^ (k + N))) :
    Summable fun k : ℕ => ‖sqterm d (r : ℂ) (k + N)‖ := by
  refine Summable.of_norm_bounded (hg := hgN.mul_left (ε / 8)) (fun k => ?_)
  rw [norm_norm]
  exact hterm k

/-- Comparison of the absolutely convergent sum with the geometric majorant. -/
theorem norm_compare {d : ℕ → ℂ} {ε : ℝ} {N : ℕ} {r : ℝ}
    (hgN : Summable fun k : ℕ => ((k + N : ℕ) : ℝ) ^ 2 * r ^ (k + N))
    (hterm : ∀ k : ℕ,
      ‖sqterm d (r : ℂ) (k + N)‖ ≤ (ε / 8) * (((k + N : ℕ) : ℝ) ^ 2 * r ^ (k + N)))
    (hnormsummable : Summable fun k : ℕ => ‖sqterm d (r : ℂ) (k + N)‖) :
    ∑' k : ℕ, ‖sqterm d (r : ℂ) (k + N)‖
      ≤ (ε / 8) * ∑' k : ℕ, (((k + N : ℕ) : ℝ) ^ 2 * r ^ (k + N)) := by
  have hle := Summable.tsum_le_tsum hterm hnormsummable (hgN.mul_left (ε / 8))
  rwa [tsum_mul_left] at hle

/-- The shifted quadratic weights are dominated by the full geometric sum. -/
theorem geom_compare {N : ℕ} {r : ℝ} (hrpos : 0 < r) (hrreal : ‖r‖ < 1) :
    ∑' k : ℕ, (((k + N : ℕ) : ℝ) ^ 2 * r ^ (k + N)) ≤ r * (1 + r) / (1 - r) ^ 3 := by
  have hgs : Summable fun m : ℕ => (m : ℝ) ^ 2 * r ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hrreal
  have hsplit := hgs.sum_add_tsum_nat_add N
  have hnonneg : (0 : ℝ) ≤ ∑ m ∈ Finset.range N, ((m : ℝ) ^ 2 * r ^ m) :=
    Finset.sum_nonneg (fun m _ => by positivity)
  have hclosed : ∑' m : ℕ, (m : ℝ) ^ 2 * r ^ m = r * (1 + r) / (1 - r) ^ 3 :=
    tsum_sq_mul_geometric_of_norm_lt_one hrreal
  linarith [hsplit, hnonneg, hclosed]

/-- Tail estimate: coefficients bounded by `ε/8` from index `N` on contribute at
most `ε/4` after the `(1-r)^3` normalization. -/
theorem sq_tail_bound {d : ℕ → ℂ} {C ε : ℝ} {N : ℕ} (hC : ∀ n, ‖d n‖ ≤ C)
    (hε : 0 < ε) (hN : ∀ n, N ≤ n → ‖d n‖ ≤ ε / 8) {r : ℝ} (hrpos : 0 < r) (hrlt : r < 1) :
    ‖∑' k : ℕ, sqterm d (r : ℂ) (k + N)‖ ≤ (ε / 8) * (r * (1 + r) / (1 - r) ^ 3) := by
  have hrreal : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_pos hrpos] using hrlt
  have hterm := pointwise_bound (d := d) hrpos hN
  have hgN := target_summable (N := N) (r := r) hrreal
  have hns := norm_summable hgN hterm
  have hnc := norm_compare hgN hterm hns
  have hgc := geom_compare (N := N) hrpos hrreal
  calc ‖∑' k : ℕ, sqterm d (r : ℂ) (k + N)‖
      ≤ ∑' k : ℕ, ‖sqterm d (r : ℂ) (k + N)‖ := norm_tsum_le_tsum_norm hns
    _ ≤ (ε / 8) * ∑' k : ℕ, (((k + N : ℕ) : ℝ) ^ 2 * r ^ (k + N)) := hnc
    _ ≤ (ε / 8) * (r * (1 + r) / (1 - r) ^ 3) :=
        mul_le_mul_of_nonneg_left hgc (by positivity)

/-- The finite prefix, scaled by `(1-r)^3`, tends to zero. -/
theorem prefix_tendsto_zero (d : ℕ → ℂ) (N : ℕ) :
    Tendsto (fun r : ℝ => (1 - (r : ℂ)) ^ 3 * ∑ n ∈ Finset.range N, sqterm d (r : ℂ) n)
      (𝓝[<] 1) (𝓝 0) := by
  have hpoly : Tendsto (fun r : ℝ => ∑ n ∈ Finset.range N, sqterm d (r : ℂ) n)
      (𝓝[<] 1) (𝓝 (∑ n ∈ Finset.range N, sqterm d ((1 : ℝ) : ℂ) n)) := by
    apply tendsto_finsetSum
    intro n _
    have hcont : Continuous fun r : ℝ => sqterm d (r : ℂ) n := by
      simp only [sqterm]
      exact continuous_const.mul (Complex.continuous_ofReal.pow n)
    exact hcont.tendsto 1 |>.mono_left nhdsWithin_le_nhds
  have hcube : Tendsto (fun r : ℝ => (1 - (r : ℂ)) ^ 3) (𝓝[<] 1) (𝓝 (((1 : ℂ) - 1) ^ 3)) := by
    have hbase : Tendsto (fun r : ℝ => (1 - (r : ℂ))) (𝓝[<] 1) (𝓝 ((1 : ℂ) - 1)) :=
      tendsto_const_nhds.sub
        (Complex.continuous_ofReal.tendsto (1 : ℝ) |>.mono_left nhdsWithin_le_nhds)
    exact hbase.pow 3
  have h := hcube.mul hpoly
  simpa using h

set_option maxHeartbeats 600000 in
/-- A coefficient sequence tending to zero has a vanishing quadratically weighted
Abel mean after the `(1-r)^3` normalization. -/
theorem abel_sq_tendsto_zero (d : ℕ → ℂ) (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (1 - (r : ℂ)) ^ 3 * ∑' n : ℕ, sqterm d (r : ℂ) n)
      (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto d hd).exists_norm_le
  have hC' : ∀ n, ‖d n‖ ≤ C := fun n => hC _ ⟨n, rfl⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hd (ε / 8) (by positivity)
  have hN' : ∀ n, N ≤ n → ‖d n‖ ≤ ε / 8 := by
    intro n hn
    have hlt : dist (d n) 0 < ε / 8 := hN n hn
    simpa [dist_eq_norm] using hlt.le
  have hpre := prefix_tendsto_zero d N
  have hsmall : ∀ᶠ r : ℝ in 𝓝[<] 1,
      ‖(1 - (r : ℂ)) ^ 3 * ∑ n ∈ Finset.range N, sqterm d (r : ℂ) n‖ ≤ ε / 2 := by
    have := (Metric.tendsto_nhds.mp hpre) (ε / 2) (by positivity)
    filter_upwards [this] with r hr
    simpa [dist_eq_norm, sub_zero] using hr.le
  filter_upwards [hsmall, Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hsmall' hrIoo
  rw [dist_eq_norm, sub_zero]
  have hrpos : (0 : ℝ) < r := hrIoo.1
  have hrlt : r < 1 := hrIoo.2
  have hrnorm : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos] using hrlt
  have hsum : Summable fun n : ℕ => sqterm d (r : ℂ) n := summable_sq_mul_abel hC' hrnorm
  have hdec : (∑ n ∈ Finset.range N, sqterm d (r : ℂ) n) + ∑' k : ℕ, sqterm d (r : ℂ) (k + N)
      = ∑' n : ℕ, sqterm d (r : ℂ) n := hsum.sum_add_tsum_nat_add N
  have htailbound := sq_tail_bound (d := d) hC' hε hN' hrpos hrlt
  have hS : ‖∑' n : ℕ, sqterm d (r : ℂ) n‖
      ≤ ‖∑ n ∈ Finset.range N, sqterm d (r : ℂ) n‖ + (ε / 8) * (r * (1 + r) / (1 - r) ^ 3) := by
    rw [← hdec]
    exact (norm_add_le _ _).trans (by linarith [htailbound])
  have hnormeq : ‖(1 - (r : ℂ)) ^ 3‖ = (1 - r) ^ 3 := by
    have hpt : (1 - (r : ℂ)) = (((1 - r : ℝ)) : ℂ) := by push_cast; ring
    rw [norm_pow, hpt, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hPbound : (1 - r) ^ 3 * ‖∑ n ∈ Finset.range N, sqterm d (r : ℂ) n‖ ≤ ε / 2 := by
    have h := hsmall'
    rw [norm_mul, hnormeq] at h
    exact h
  have hcube_nn : (0 : ℝ) ≤ (1 - r) ^ 3 := by
    have : (0 : ℝ) ≤ 1 - r := by linarith
    positivity
  have hcollapse : (1 - r) ^ 3 * ((ε / 8) * (r * (1 + r) / (1 - r) ^ 3))
      = (ε / 8) * (r * (1 + r)) := by
    have hrne : (1 : ℝ) - r ≠ 0 := by linarith
    field_simp
    try ring
  have hmain : ‖(1 - (r : ℂ)) ^ 3 * ∑' n : ℕ, sqterm d (r : ℂ) n‖
      ≤ ε / 2 + (ε / 8) * (r * (1 + r)) := by
    rw [norm_mul, hnormeq]
    have hstep := mul_le_mul_of_nonneg_left hS hcube_nn
    have hexp : (1 - r) ^ 3 * (‖∑ n ∈ Finset.range N, sqterm d (r : ℂ) n‖
        + (ε / 8) * (r * (1 + r) / (1 - r) ^ 3))
        = (1 - r) ^ 3 * ‖∑ n ∈ Finset.range N, sqterm d (r : ℂ) n‖
          + (ε / 8) * (r * (1 + r)) := by
      rw [mul_add, hcollapse]
    linarith [hstep, hPbound, hexp]
  have hr2 : r * (1 + r) ≤ 2 := by nlinarith
  have hstep2 : (ε / 8) * (r * (1 + r)) ≤ (ε / 8) * 2 :=
    mul_le_mul_of_nonneg_left hr2 (by positivity)
  linarith [hmain, hstep2, hε]

/-- The constant-coefficient quadratic masses, normalized by `(1-r)^3`, tend to `2`. -/
theorem const_geom_limit :
    Tendsto (fun r : ℝ =>
      (1 - (r : ℂ)) ^ 3 * ∑' n : ℕ, sqterm (fun _ => (1 : ℂ)) (r : ℂ) n) (𝓝[<] 1) (𝓝 2) := by
  have hsq : ∀ r : ℝ, (∑' n : ℕ, sqterm (fun _ => (1 : ℂ)) (r : ℂ) n)
      = ∑' n : ℕ, (n : ℂ) ^ 2 * (r : ℂ) ^ n := by
    intro r
    apply tsum_congr
    intro n
    simp only [sqterm]
    ring
  have hval : ∀ᶠ r : ℝ in 𝓝[<] 1,
      (1 - (r : ℂ)) ^ 3 * ∑' n : ℕ, sqterm (fun _ => (1 : ℂ)) (r : ℂ) n
        = (r : ℂ) * (1 + (r : ℂ)) := by
    have hclosed : ∀ᶠ r : ℝ in 𝓝[<] 1,
        ∑' n : ℕ, sqterm (fun _ => (1 : ℂ)) (r : ℂ) n
          = (r : ℂ) * (1 + (r : ℂ)) / (1 - (r : ℂ)) ^ 3 := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hrIoo
      have hrnorm : ‖(r : ℂ)‖ < 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrIoo.1] using hrIoo.2
      rw [hsq r]
      exact tsum_sq_mul_geometric_of_norm_lt_one hrnorm
    filter_upwards [hclosed, self_mem_nhdsWithin] with r hrclosed hrlt
    have hrlt' : r < 1 := hrlt
    rw [hrclosed]
    have hrne : (1 - (r : ℂ)) ≠ 0 := by
      intro h0
      have h1 : (r : ℂ) = 1 := by linear_combination -h0
      have h2 : r = 1 := by exact_mod_cast h1
      linarith
    field_simp
    try ring
  refine (tendsto_congr' hval).2 ?_
  have hr : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[<] 1) (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.tendsto (1 : ℝ) |>.mono_left nhdsWithin_le_nhds
  have hr1 : Tendsto (fun r : ℝ => (r : ℂ) * (1 + (r : ℂ))) (𝓝[<] 1) (𝓝 ((1 : ℂ) * (1 + 1))) :=
    hr.mul (tendsto_const_nhds.add hr)
  have hlim : ((1 : ℂ) * (1 + 1)) = (2 : ℂ) := by norm_num
  rw [hlim] at hr1
  exact hr1

set_option maxHeartbeats 600000 in
/-- If `c n → L` then the quadratically weighted Abel mean of `c`, normalized by
`(1-r)^3`, tends to `2 L`. -/
theorem abel_sq_weight (c : ℕ → ℂ) (L : ℂ) (hc : Tendsto c atTop (𝓝 L)) :
    Tendsto (fun r : ℝ => (1 - (r : ℂ)) ^ 3 * ∑' n : ℕ, sqterm c (r : ℂ) n)
      (𝓝[<] 1) (𝓝 (2 * L)) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto c hc).exists_norm_le
  have hC' : ∀ n, ‖c n‖ ≤ C := fun n => hC _ ⟨n, rfl⟩
  have hzero := abel_sq_tendsto_zero (fun n => c n - L) (by simpa using hc.sub_const L)
  have hgeom := const_geom_limit.const_mul L
  have hspl : ∀ᶠ r : ℝ in 𝓝[<] 1,
      (1 - (r : ℂ)) ^ 3 * ∑' n : ℕ, sqterm c (r : ℂ) n
        = (1 - (r : ℂ)) ^ 3 * (∑' n : ℕ, sqterm (fun n => c n - L) (r : ℂ) n)
          + L * ((1 - (r : ℂ)) ^ 3 * ∑' n : ℕ, sqterm (fun _ => (1 : ℂ)) (r : ℂ) n) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hrIoo
    have hrnorm : ‖(r : ℂ)‖ < 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrIoo.1] using hrIoo.2
    have hs1 : Summable fun n : ℕ => sqterm (fun n => c n - L) (r : ℂ) n :=
      summable_sq_mul_abel (fun n => by
        calc ‖c n - L‖ ≤ ‖c n‖ + ‖L‖ := norm_sub_le _ _
          _ ≤ C + ‖L‖ := by linarith [hC' n]) hrnorm
    have hs2 : Summable fun n : ℕ => L * sqterm (fun _ => (1 : ℂ)) (r : ℂ) n :=
      (summable_sq_mul_abel (d := fun _ => (1 : ℂ)) (C := 1) (fun n => by simp) hrnorm).mul_left L
    have hpt : ∀ n : ℕ, sqterm c (r : ℂ) n
        = sqterm (fun n => c n - L) (r : ℂ) n + L * sqterm (fun _ => (1 : ℂ)) (r : ℂ) n := by
      intro n
      simp only [sqterm]
      ring
    have hsum : ∑' n : ℕ, sqterm c (r : ℂ) n
        = (∑' n : ℕ, sqterm (fun n => c n - L) (r : ℂ) n)
          + L * ∑' n : ℕ, sqterm (fun _ => (1 : ℂ)) (r : ℂ) n := by
      rw [tsum_congr hpt, hs1.tsum_add hs2, tsum_mul_left]
    rw [hsum]
    ring
  refine (tendsto_congr' hspl).2 ?_
  have hsum := hzero.add hgeom
  simpa [zero_add, mul_comm, mul_left_comm, mul_assoc] using hsum

#print axioms sq_tail_bound
#print axioms abel_sq_tendsto_zero
#print axioms const_geom_limit
#print axioms abel_sq_weight

end NonAlgebraicity
