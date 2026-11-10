import FJLaurentRadial
import FJSparseRadialLog
import FJRadialFinite

/-! Shared candidate; see focused/runs/final62/result.json for validation. The coefficient-only PeriodicJumpJet hypothesis is converted
into a genuine real radial logarithm conclusion. No R/log assumption appears
among the premises. Actual extremal tournament F/J is NOT asserted here. -/
noncomputable section
open Filter Topology Finset
namespace FJPeriodicJumpRadial
open FJLaurentRadial

def BoundedCoefficients (a : ℕ→ℂ) : Prop := ∃ C : ℝ,0≤C ∧ ∀ n,‖a n‖≤C

lemma BoundedCoefficients.add {a b : ℕ→ℂ} (ha : BoundedCoefficients a)
    (hb : BoundedCoefficients b) : BoundedCoefficients (fun n => a n+b n) := by
  obtain ⟨C,hC,hCa⟩ := ha
  obtain ⟨D,hD,hDb⟩ := hb
  exact ⟨C+D,add_nonneg hC hD,fun n =>
    (norm_add_le (a n) (b n)).trans (add_le_add (hCa n) (hDb n))⟩

lemma BoundedCoefficients.sub {a b : ℕ→ℂ} (ha : BoundedCoefficients a)
    (hb : BoundedCoefficients b) : BoundedCoefficients (fun n => a n-b n) := by
  obtain ⟨C,hC,hCa⟩ := ha
  obtain ⟨D,hD,hDb⟩ := hb
  exact ⟨C+D,add_nonneg hC hD,fun n =>
    (norm_sub_le (a n) (b n)).trans (add_le_add (hCa n) (hDb n))⟩

lemma BoundedCoefficients.const_mul {a : ℕ→ℂ} (ha : BoundedCoefficients a)
    (κ : ℂ) : BoundedCoefficients (fun n => κ*a n) := by
  obtain ⟨C,hC,hCa⟩ := ha
  refine ⟨‖κ‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hCa n) (norm_nonneg _)

lemma BoundedCoefficients.finset_sum (s : Finset ℕ) (c : ℕ→ℕ→ℂ)
    (hc : ∀ j∈s,BoundedCoefficients (c j)) :
    BoundedCoefficients (fun n => ∑ j∈s,c j n) := by
  classical
  revert hc
  induction s using Finset.induction_on with
  | empty => intro hc; exact ⟨0,le_rfl,by simp⟩
  | @insert j s hj ih =>
    intro hc
    have h := (hc j (by simp)).add (ih (fun k hk => hc k (by simp [hk])))
    simpa only [Finset.sum_insert hj] using h

def radialAt (a : ℕ→ℂ) (ω : ℂ) : ℝ→ℂ :=
  FJRadialTail.radial (fun n => a n*ω^n)

lemma radialAt_eq (a : ℕ→ℂ) (ω : ℂ) (x : ℝ) :
    radialAt a ω x = ∑' n,a n*(ω*(x : ℂ))^n := by
  unfold radialAt FJRadialTail.radial FJRadialTail.jet FJRadialTail.term
  simp only [Nat.descFactorial_zero,Nat.cast_one,mul_one,Nat.sub_zero,mul_pow]
  apply tsum_congr
  intro n
  ring

lemma upgrade_eventual_decay (e : ℕ→ℂ) (d N : ℕ) (C : ℝ) (hC : 0≤C)
    (he : ∀ n, N≤n → 0<n → ‖e n‖≤C/(n : ℝ)^d) :
    ∃ K : ℝ,0≤K ∧ ∀ n,0<n → ‖e n‖≤K/(n : ℝ)^d := by
  let P : ℝ := ∑ i∈range N,‖e i‖*(i : ℝ)^d
  have hP : 0≤P := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨C+P,by positivity,?_⟩
  intro n hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  by_cases hN : N≤n
  · exact (he n hN hn).trans
      (div_le_div_of_nonneg_right (by linarith) (by positivity))
  · apply (le_div_iff₀ (pow_pos hn0 d)).mpr
    have hp : ‖e n‖*(n : ℝ)^d≤P :=
      Finset.single_le_sum (f := fun i : ℕ => ‖e i‖*(i : ℝ)^d) (s := range N) (a := n) (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
    linarith

lemma bounded_of_decay (e : ℕ→ℂ) (d : ℕ) (C : ℝ) (hC : 0≤C)
    (he : ∀ n,0<n → ‖e n‖≤C/(n : ℝ)^d) : BoundedCoefficients e := by
  refine ⟨‖e 0‖+C,by positivity,?_⟩
  intro n
  by_cases hn : n=0
  · subst n; linarith
  · have hnpos : 0<n := by omega
    have hn1 : (1 : ℝ)≤n := by exact_mod_cast hnpos
    have h := (he n hnpos).trans (div_le_self hC (one_le_pow₀ hn1))
    linarith [norm_nonneg (e 0)]

lemma terms_summable {a : ℕ→ℂ} (ha : BoundedCoefficients a) (h : ℕ)
    {x : ℝ} (hx : x∈Set.Ioo 0 1) :
    Summable (fun n => FJRadialTail.term a h n (x : ℂ)) := by
  obtain ⟨C,hC,hCa⟩ := ha
  have hxn : ‖(x : ℂ)‖<1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx.1] using hx.2
  let R : ℝ := (‖(x : ℂ)‖+1)/2
  exact FJRadialTail.term_summable hC hCa
    (by dsimp [R]; linarith [norm_nonneg (x : ℂ)] : 0<R)
    (by dsimp [R]; linarith : R<1) h
    (by dsimp [R]; linarith : ‖(x : ℂ)‖≤R)

lemma derivative_eq_jet {a : ℕ→ℂ} (ha : BoundedCoefficients a) (h : ℕ)
    {x : ℝ} (hx : x∈Set.Ioo 0 1) :
    iteratedDeriv h (FJRadialTail.radial a) x=FJRadialTail.jet a h (x : ℂ) := by
  obtain ⟨C,hC,hCa⟩ := ha
  exact FJRadialTail.iterated_radial hC hCa h x hx

/-- Finite linearity is proved on the absolutely convergent derivative
series, not by differentiating a coefficient big-O identity. -/
lemma derivative_linear_assembly (s : Finset ℕ) (a d e : ℕ→ℂ) (c : ℕ→ℕ→ℂ)
    (κ : ℂ) (ha : BoundedCoefficients a) (hd : BoundedCoefficients d)
    (he : BoundedCoefficients e) (hc : ∀ j∈s,BoundedCoefficients (c j))
    (hcoef : ∀ n,a n=(∑ j∈s,c j n)-κ*d n+e n) (h : ℕ)
    {x : ℝ} (hx : x∈Set.Ioo 0 1) :
    iteratedDeriv h (FJRadialTail.radial a) x =
      (∑ j∈s,iteratedDeriv h (FJRadialTail.radial (c j)) x) -
        κ*iteratedDeriv h (FJRadialTail.radial d) x +
          iteratedDeriv h (FJRadialTail.radial e) x := by
  have hC := hasSum_sum (s := s) (fun j hj => (terms_summable (hc j hj) h hx).hasSum)
  have hD := (terms_summable hd h hx).hasSum.mul_left κ
  have hE := (terms_summable he h hx).hasSum
  have hs := (hC.sub hD).add hE
  have hs' : HasSum (fun n => FJRadialTail.term a h n (x : ℂ))
      ((∑ j∈s,FJRadialTail.jet (c j) h (x : ℂ))-
        κ*FJRadialTail.jet d h (x : ℂ)+FJRadialTail.jet e h (x : ℂ)) := by
    dsimp only [FJRadialTail.jet]
    convert hs using 1
    ext n
    unfold FJRadialTail.term
    rw [hcoef n]
    simp only [sub_mul, add_mul, Finset.sum_mul, Pi.add_apply, Pi.sub_apply]
    ring
  rw [derivative_eq_jet ha h hx,derivative_eq_jet hd h hx,derivative_eq_jet he h hx]
  have hcj : (∑ j∈s,iteratedDeriv h (FJRadialTail.radial (c j)) x) =
      ∑ j∈s,FJRadialTail.jet (c j) h (x : ℂ) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact derivative_eq_jet (hc j hj) h hx
  rw [hcj]
  exact hs'.tsum_eq

lemma twisted_antiperiodic (u : ℕ→ℂ) {b : ℕ} (hu : Function.Periodic u b)
    {ω : ℂ} (hω : ω^b= -1) : Function.Antiperiodic (fun n => u n*ω^n) b := by
  intro n
  dsimp only
  rw [hu n,pow_add,hω]
  ring

/-- Abstract one-layer R, with only the periodic coefficient jet as input.
Coefficient boundedness is derived, not an additional assumption.
The limit formulation is stronger than the O(1) remainder requested by R. -/
theorem periodicJumpJet_radial (a : ℕ→ℂ) {b k : ℕ} (hb : 0<b) (κ ω : ℂ)
    (hω : IsPrimitiveRoot ω (2*b))
    (hjet : FJRadialFinite.PeriodicJumpJet a b k κ) :
    (∀ h<k,FiniteLimit (iteratedDeriv h (radialAt a ω))) ∧
      FiniteLimit (fun x : ℝ => iteratedDeriv k (radialAt a ω) x -
        (κ/(2*b : ℕ))*(Real.log (1-x) : ℂ)) := by
  classical
  obtain ⟨u,hu,C,hC,N,herr⟩ := hjet
  let q : ℕ := 2*b
  have hq : 0<q := by dsimp [q]; omega
  have hunit : ‖ω‖=1 := hω.norm'_eq_one (by omega)
  have hhalf : ω^b= -1 := FJRadialFinite.primitive_half_power hb hω
  let v : ℕ→ℕ→ℂ := fun j n => u j n*ω^n
  let c : ℕ→ℕ→ℂ := fun j n => v j n/(n : ℂ)^j
  let d : ℕ→ℂ := FJSparseRadialLog.coefficient q (k+1)
  let A : ℕ→ℂ := fun n => a n*ω^n
  let e : ℕ→ℂ := fun n => A n-((∑ j∈range (k+2),c j n)-κ*d n)
  have hv : ∀ j∈range (k+2),Function.Antiperiodic (v j) b := by
    intro j hj
    exact twisted_antiperiodic (u j) (hu j (by
      have hjlt := Finset.mem_range.mp hj
      omega)) hhalf
  have hdc : BoundedCoefficients d :=
    ⟨1,by norm_num,FJSparseRadialLog.coefficient_bounded q (k+1) (by omega)⟩
  have hcc : ∀ j∈range (k+2),BoundedCoefficients (c j) := by
    intro j hj
    let K : ℝ := ∑ t∈range b,‖v j t‖
    have hK : 0≤K := Finset.sum_nonneg (fun t _ => norm_nonneg _)
    exact ⟨K,hK,coefficient_div_bounded hK
      (FJAntiperiodicRational.antiperiodic_bound hb (hv j hj)) j⟩
  have heq : ∀ n,e n=(a n-((∑ j∈range (k+2),u j n/(n : ℂ)^j)-
      if q∣n then κ/(n : ℂ)^(k+1) else 0))*ω^n := by
    intro n
    have hs : (∑ j∈range (k+2),c j n)=
        (∑ j∈range (k+2),u j n/(n : ℂ)^j)*ω^n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [c,v]
      ring
    dsimp [e,A]
    rw [hs]
    by_cases hn : q∣n
    · have hp : ω^n=1 := hω.pow_eq_one_iff_dvd n |>.mpr hn
      simp only [d,FJSparseRadialLog.coefficient,if_pos hn,hp,mul_one]
      ring
    · simp only [d,FJSparseRadialLog.coefficient,if_neg hn,mul_zero,sub_zero]
      ring
  have hedec : ∀ n,N≤n → 0<n → ‖e n‖≤C/(n : ℝ)^(k+2) := by
    intro n hn hnp
    rw [heq n,norm_mul,norm_pow,hunit,one_pow,mul_one]
    exact herr n hn hnp
  obtain ⟨K,hK,hKe⟩ := upgrade_eventual_decay e (k+2) N C hC hedec
  have hec : BoundedCoefficients e := bounded_of_decay e (k+2) K hK hKe
  have hcoef : ∀ n,A n=(∑ j∈range (k+2),c j n)-κ*d n+e n := by
    intro n
    dsimp [e]
    ring
  have hAc : BoundedCoefficients A := by
    obtain ⟨M,hM,hMa⟩ :=
      ((BoundedCoefficients.finset_sum (range (k+2)) c hcc).sub
        (hdc.const_mul κ)).add hec
    exact ⟨M,hM,fun n => by rw [hcoef n]; exact hMa n⟩
  have hnonres : ∀ h : ℕ,FiniteLimit
      (fun x : ℝ => ∑ j∈range (k+2),iteratedDeriv h (FJRadialTail.radial (c j)) x) := by
    intro h
    apply FiniteLimit.finset_sum
    intro j hj
    exact inverse_radial_derivatives_finite hb (hv j hj) j h
  have htail : ∀ h≤k,FiniteLimit (iteratedDeriv h (FJRadialTail.radial e)) := by
    intro h hh
    obtain ⟨M,hM,hMe⟩ := hec
    exact ⟨_,FJRadialTail.iterated_radial_tendsto hM hMe h
      (FJRadialTail.falling_moment_summable hK hKe hh)⟩
  have hlinear := derivative_linear_assembly (range (k+2)) A d e c κ
    hAc hdc hec hcc hcoef
  constructor
  · intro h hh
    have hsp : FiniteLimit (iteratedDeriv h (FJRadialTail.radial d)) :=
      ⟨_,FJSparseRadialLog.lower_radial_tendsto q k h hh⟩
    have hlim := ((hnonres h).sub (hsp.const_mul κ)).add (htail h (by omega))
    apply hlim.congr
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hx
    exact (hlinear _ hx).symm
  · have hsp : FiniteLimit (fun x : ℝ =>
        iteratedDeriv k (FJRadialTail.radial d) x+(Real.log (1-x) : ℂ)/(q : ℂ)) :=
      ⟨_,FJSparseRadialLog.highest_radial_log_tendsto q hq k⟩
    have h := ((hnonres k).sub (hsp.const_mul κ)).add (htail k le_rfl)
    apply h.congr
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with x hx
    have hl := hlinear k hx
    change _ = iteratedDeriv k (FJRadialTail.radial A) x-
      (κ/(q : ℂ))*(Real.log (1-x) : ℂ)
    rw [hl]
    ring

end FJPeriodicJumpRadial
#print axioms FJPeriodicJumpRadial.derivative_linear_assembly
#print axioms FJPeriodicJumpRadial.periodicJumpJet_radial
