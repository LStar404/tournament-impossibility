import FJFallingCorrection
import FJAntiperiodicRational
import FJAntiperiodicAbel
import FJRadialTail

/-! Shared candidate; see focused/runs/final62/result.json for validation. Finite Laurent assembly for nonresonant antiperiodic
coefficients, ending in limits of actual real radial derivatives. -/
noncomputable section
open Filter Topology Finset
namespace FJLaurentRadial
open FJFallingCorrection

def FiniteLimit (f : ℝ→ℂ) : Prop := ∃ L : ℂ, Tendsto f (𝓝[<] 1) (𝓝 L)

lemma FiniteLimit.congr {f g : ℝ→ℂ} (hf : FiniteLimit f)
    (hfg : f=ᶠ[𝓝[<] 1]g) : FiniteLimit g := by
  obtain ⟨L,hL⟩ := hf
  exact ⟨L,hL.congr' hfg⟩

lemma FiniteLimit.const_mul {f : ℝ→ℂ} (hf : FiniteLimit f) (c : ℂ) :
    FiniteLimit (fun x => c*f x) := by
  obtain ⟨L,hL⟩ := hf
  exact ⟨c*L,hL.const_mul c⟩

lemma FiniteLimit.add {f g : ℝ→ℂ} (hf : FiniteLimit f) (hg : FiniteLimit g) :
    FiniteLimit (fun x => f x+g x) := by
  obtain ⟨L,hL⟩ := hf
  obtain ⟨M,hM⟩ := hg
  exact ⟨L+M,hL.add hM⟩

lemma FiniteLimit.sub {f g : ℝ→ℂ} (hf : FiniteLimit f) (hg : FiniteLimit g) :
    FiniteLimit (fun x => f x-g x) := by
  obtain ⟨L,hL⟩ := hf
  obtain ⟨M,hM⟩ := hg
  exact ⟨L-M,hL.sub hM⟩

lemma FiniteLimit.finset_sum {ι : Type*} (s : Finset ι) (f : ι→ℝ→ℂ)
    (hf : ∀ i∈s,FiniteLimit (f i)) : FiniteLimit (fun x => ∑ i∈s,f i x) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro hf; exact ⟨0,by simpa using tendsto_const_nhds⟩
  | @insert i s hi ih =>
    intro hf
    have h := (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))
    simpa only [Finset.sum_insert hi] using h

lemma coefficient_div_bounded {v : ℕ→ℂ} {C : ℝ} (hC : 0≤C)
    (hv : ∀ n,‖v n‖≤C) (d : ℕ) : ∀ n,‖v n/(n : ℂ)^d‖≤C := by
  intro n
  by_cases hn : n=0
  · subst n
    cases d with
    | zero => simpa using hv 0
    | succ d => simpa using hC
  · have hnpos : 0<n := by omega
    have hn1 : (1 : ℝ)≤n := by exact_mod_cast hnpos
    rw [norm_div,norm_pow,Complex.norm_natCast]
    exact (div_le_self (norm_nonneg _) (one_le_pow₀ hn1)).trans (hv n)

def factorialMoment (v : ℕ→ℂ) (h : ℕ) (z : ℂ) : ℂ :=
  ∑' n,v n*(n.descFactorial h : ℂ)*z^n

def moment (v : ℕ→ℂ) (m : ℕ) (z : ℂ) : ℂ := ∑' n : ℕ,(n : ℂ)^m*v n*z^n

def positiveMonomial (v : ℕ→ℂ) (m d : ℕ) (z : ℂ) : ℂ :=
  ∑' n,v (n+1)*(((n+1 : ℕ) : ℂ)^m/((n+1 : ℕ) : ℂ)^d)*z^(n+1)

def positivePolynomial (v : ℕ→ℂ) (p : Polynomial ℂ) (d : ℕ) (z : ℂ) : ℂ :=
  ∑' n,v (n+1)*(p.eval ((n+1 : ℕ) : ℂ)/((n+1 : ℕ) : ℂ)^d)*z^(n+1)

lemma factorialMoment_summable {v : ℕ→ℂ} {b : ℕ} (hb : 0<b)
    (hv : Function.Antiperiodic v b) (h : ℕ) {z : ℂ} (hz : ‖z‖<1) :
    Summable (fun n => v n*(n.descFactorial h : ℂ)*z^n) := by
  let C : ℝ := ∑ t∈range b,‖v t‖
  have hC : 0≤C := Finset.sum_nonneg (fun t _ => norm_nonneg (v t))
  have hc := FJAntiperiodicRational.antiperiodic_bound hb hv
  have hs : Summable (fun n : ℕ => C*((n : ℝ)^h*‖z‖^n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one h (by simpa using hz)).mul_left C
  apply hs.of_norm_bounded
  intro n
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_natCast]
  have hd : (n.descFactorial h : ℝ)≤(n : ℝ)^h := by
    exact_mod_cast Nat.descFactorial_le_pow n h
  calc
    _ ≤ C*(n : ℝ)^h*‖z‖^n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hc n) hd (by positivity) hC) (by positivity)
    _ = _ := by ring

lemma factorialMoment_finite {v : ℕ→ℂ} {b : ℕ} (hb : 0<b)
    (hv : Function.Antiperiodic v b) (h : ℕ) :
    FiniteLimit (fun x : ℝ => factorialMoment v h (x : ℂ)) := by
  let C : ℝ := ∑ t∈range b,‖v t‖
  have hC : 0≤C := Finset.sum_nonneg (fun t _ => norm_nonneg (v t))
  have hc := FJAntiperiodicRational.antiperiodic_bound hb hv
  have he : FJRadialTail.radial v =
      (fun x : ℝ => FJAntiperiodicRational.series v (x : ℂ)) := by
    funext x
    simp [FJRadialTail.radial,FJRadialTail.jet,FJRadialTail.term,
      FJAntiperiodicRational.series]
  have hd := FJAntiperiodicRational.radial_derivatives_tendsto hb hv h
  rw [← he] at hd
  have hx : Tendsto (fun x : ℝ => (x : ℂ)^h) (𝓝[<] 1) (𝓝 (1 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)
      |>.mono_left nhdsWithin_le_nhds).pow h
  refine ⟨1 * iteratedDeriv h (fun x : ℝ => FJAntiperiodicRational.rationalExtension v b (x : ℂ)) 1, ?_⟩
  apply (hx.mul hd).congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hxi
  rw [FJRadialTail.iterated_radial hC hc h x hxi]
  exact (weighted_jet_identity v h (x : ℂ)).symm

lemma moment_hasSum {v : ℕ→ℂ} {b : ℕ} (hb : 0<b)
    (hv : Function.Antiperiodic v b) (m : ℕ) {z : ℂ} (hz : ‖z‖<1) :
    HasSum (fun n : ℕ => (n : ℂ)^m*v n*z^n)
      (∑ h∈range (m+1),(Nat.stirlingSecond m h : ℂ)*factorialMoment v h z) := by
  have hs := hasSum_sum (s := range (m+1)) (fun h _ =>
    (factorialMoment_summable hb hv h hz).hasSum.mul_left (Nat.stirlingSecond m h : ℂ))
  change HasSum _ (∑ h ∈ range (m+1), (Nat.stirlingSecond m h : ℂ) * (∑' n, v n*(n.descFactorial h : ℂ)*z^n))
  convert hs using 1
  ext n
  have hn : (n : ℂ)^m = ∑ h∈range (m+1),
      (Nat.stirlingSecond m h : ℂ)*(n.descFactorial h : ℂ) := by
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial n m
  rw [hn]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  ring

lemma moment_finite {v : ℕ→ℂ} {b : ℕ} (hb : 0<b)
    (hv : Function.Antiperiodic v b) (m : ℕ) :
    FiniteLimit (fun x : ℝ => moment v m (x : ℂ)) := by
  have h := FiniteLimit.finset_sum (range (m+1))
    (fun h x => (Nat.stirlingSecond m h : ℂ)*factorialMoment v h (x : ℂ))
    (fun h _ => (factorialMoment_finite hb hv h).const_mul _)
  apply h.congr
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hx
  exact (moment_hasSum hb hv m (z := (x : ℂ))
    (by simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx.1] using hx.2)).tsum_eq.symm

lemma positiveMonomial_summable {v : ℕ→ℂ} {b : ℕ} (hb : 0<b)
    (hv : Function.Antiperiodic v b) (m d : ℕ) {z : ℂ} (hz : ‖z‖<1) :
    Summable (fun n => v (n+1)*(((n+1 : ℕ) : ℂ)^m/((n+1 : ℕ) : ℂ)^d)*z^(n+1)) := by
  let C : ℝ := ∑ t∈range b,‖v t‖
  have hC : 0≤C := Finset.sum_nonneg (fun t _ => norm_nonneg (v t))
  have hc := FJAntiperiodicRational.antiperiodic_bound hb hv
  have hdiv := coefficient_div_bounded hC hc d
  have hs : Summable (fun n : ℕ => C*((n : ℝ)^m*‖z‖^n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one m (by simpa using hz)).mul_left C
  have hs' := (summable_nat_add_iff 1).mpr hs
  apply hs'.of_norm_bounded
  intro n
  have he : v (n+1)*(((n+1 : ℕ) : ℂ)^m/((n+1 : ℕ) : ℂ)^d) =
      (v (n+1)/((n+1 : ℕ) : ℂ)^d)*((n+1 : ℕ) : ℂ)^m := by ring
  rw [he,norm_mul,norm_mul,norm_pow,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ C*((n+1 : ℕ) : ℝ)^m*‖z‖^(n+1) := by gcongr; exact hdiv (n+1)
    _ = _ := by ring

/-- All Laurent monomials at positive integer indices. -/
lemma positiveMonomial_finite {v : ℕ→ℂ} {b : ℕ} (hb : 0<b)
    (hv : Function.Antiperiodic v b) (m d : ℕ) :
    FiniteLimit (fun x : ℝ => positiveMonomial v m d (x : ℂ)) := by
  by_cases hdm : d ≤ m
  · have h := (moment_finite hb hv (m-d)).sub
      (show FiniteLimit (fun _ : ℝ => (0 : ℂ)^(m-d)*v 0) from ⟨_,tendsto_const_nhds⟩)
    apply h.congr
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hx
    have hxn : ‖(x : ℂ)‖<1 := by
      simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx.1] using hx.2
    have hs := (moment_hasSum hb hv (m-d) hxn).summable
    have he := hs.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one,pow_zero,mul_one] at he
    have hp : positiveMonomial v m d (x : ℂ) =
        ∑' n, ((n+1 : ℕ) : ℂ)^(m-d)*v (n+1)*(x : ℂ)^(n+1) := by
      apply tsum_congr
      intro n
      have hr : ((n+1 : ℕ) : ℂ)^m/((n+1 : ℕ) : ℂ)^d =
          ((n+1 : ℕ) : ℂ)^(m-d) := by
        simpa only [div_eq_mul_inv] using
          (pow_sub₀ ((n+1 : ℕ) : ℂ)
            (by exact_mod_cast (show n+1≠0 by omega)) hdm).symm
      rw [hr]
      ring
    rw [hp]
    change (∑' n : ℕ,(n : ℂ)^(m-d)*v n*(x : ℂ)^n)-_=_
    simp only [Nat.cast_zero] at he
    linear_combination -he
  · have hmd : 0<d-m := by omega
    obtain ⟨L,hL⟩ := FJAntiperiodicAbel.inverse_weighted_abel hb hv (d-m) hmd
    have hx : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[<] 1) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.tendsto (1 : ℝ) |>.mono_left nhdsWithin_le_nhds
    refine ⟨L, ?_⟩
    have ht := hx.mul hL
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [] with x
    unfold positiveMonomial
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hn : ((n+1 : ℕ) : ℂ)≠0 := by exact_mod_cast (show n+1≠0 by omega)
    have hr : ((n+1 : ℕ) : ℂ)^m/((n+1 : ℕ) : ℂ)^d =
        1/((n+1 : ℕ) : ℂ)^(d-m) := by
      conv_lhs => rw [show d=m+(d-m) by omega,pow_add]
      field_simp [hn]
    rw [hr,pow_succ]
    ring

/-- Finite polynomial/Laurent assembly; no convergence of a formal infinite
asymptotic expansion is used. -/
lemma positivePolynomial_finite {v : ℕ→ℂ} {b : ℕ} (hb : 0<b)
    (hv : Function.Antiperiodic v b) (p : Polynomial ℂ) (d : ℕ) :
    FiniteLimit (fun x : ℝ => positivePolynomial v p d (x : ℂ)) := by
  have h := FiniteLimit.finset_sum p.support
    (fun m x => p.coeff m*positiveMonomial v m d (x : ℂ))
    (fun m _ => (positiveMonomial_finite hb hv m d).const_mul _)
  apply h.congr
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hx
  have hxn : ‖(x : ℂ)‖<1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx.1] using hx.2
  have hs := hasSum_sum (s := p.support) (fun m _ =>
    (positiveMonomial_summable hb hv m d hxn).hasSum.mul_left (p.coeff m))
  have hs' : HasSum (fun n => v (n+1)*(p.eval ((n+1 : ℕ) : ℂ)/
      ((n+1 : ℕ) : ℂ)^d)*(x : ℂ)^(n+1))
      (∑ m∈p.support,p.coeff m*positiveMonomial v m d (x : ℂ)) := by
    dsimp only [positiveMonomial] at *
    convert hs using 1
    ext n
    rw [Polynomial.eval_eq_sum]
    simp only [Polynomial.sum,Finset.sum_div,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    ring
  exact hs'.tsum_eq.symm

/-- Final nonresonant endpoint: the actual real derivatives of v_n/n^d
have finite limits at every order, solely from coefficient antiperiodicity. -/
theorem inverse_radial_derivatives_finite {v : ℕ→ℂ} {b : ℕ} (hb : 0<b)
    (hv : Function.Antiperiodic v b) (d h : ℕ) :
    FiniteLimit (iteratedDeriv h (FJRadialTail.radial (fun n => v n/(n : ℂ)^d))) := by
  let c : ℕ→ℂ := fun n => v n/(n : ℂ)^d
  let C : ℝ := ∑ t∈range b,‖v t‖
  have hC : 0≤C := Finset.sum_nonneg (fun t _ => norm_nonneg (v t))
  have hc : ∀ n,‖c n‖≤C :=
    coefficient_div_bounded hC (FJAntiperiodicRational.antiperiodic_bound hb hv) d
  have hP := positivePolynomial_finite hb hv (descPochhammer ℂ h) d
  obtain ⟨L,hL⟩ := hP
  have hx : Tendsto (fun x : ℝ => (x : ℂ)^h) (𝓝[<] 1) (𝓝 (1 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)
      |>.mono_left nhdsWithin_le_nhds).pow h
  have ht := (hL.const_add (c 0*((0 : ℕ).descFactorial h : ℂ))).div hx
    (by norm_num : (1 : ℂ)≠0)
  refine ⟨c 0*((0 : ℕ).descFactorial h : ℂ)+L, ?_⟩
  simp only [div_one] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hxi
  have hxn : (x : ℂ)≠0 := by exact_mod_cast (ne_of_gt hxi.1)
  have hnorm : ‖(x : ℂ)‖<1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxi.1] using hxi.2
  have hs : Summable (fun n => c n*(n.descFactorial h : ℂ)*(x : ℂ)^n) := by
    let R : ℝ := (‖(x : ℂ)‖+1)/2
    have hR : 0<R := by dsimp [R]; linarith [norm_nonneg (x : ℂ)]
    have hR1 : R<1 := by dsimp [R]; linarith
    have hj := FJRadialTail.term_summable hC hc hR hR1 h
      (by dsimp [R]; linarith : ‖(x : ℂ)‖≤R)
    convert hj.mul_left ((x : ℂ)^h) using 1
    ext n
    by_cases hn : h≤n
    · simp only [FJRadialTail.term]
      rw [pow_sub₀ _ hxn hn]
      field_simp
    · simp [FJRadialTail.term,Nat.descFactorial_of_lt (show n<h by omega)]
  have he := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,pow_zero,mul_one] at he
  have hp : (∑' n,c (n+1)*((n+1).descFactorial h : ℂ)*(x : ℂ)^(n+1)) =
      positivePolynomial v (descPochhammer ℂ h) d (x : ℂ) := by
    apply tsum_congr
    intro n
    rw [descPochhammer_eval_eq_descFactorial]
    dsimp [c]
    ring
  rw [hp,weighted_jet_identity] at he
  rw [FJRadialTail.iterated_radial hC hc h x hxi]
  apply (div_eq_iff (pow_ne_zero h hxn)).mpr
  simpa only [mul_comm] using he

end FJLaurentRadial
#print axioms FJLaurentRadial.positivePolynomial_finite
#print axioms FJLaurentRadial.inverse_radial_derivatives_finite
