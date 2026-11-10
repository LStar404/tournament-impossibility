import ActualPhysicalExponentialCandidate
/-! General scalar restoration. General capped case; independent deleted factors retained. -/
set_option autoImplicit false
noncomputable section
namespace GeneralScalarRestorationCandidate
open Matrix Finset TournamentHamiltonian ActualTournamentPrescalingBounds
open ActualPrescalingNormalization ActualRecoveryUpperCandidate PhysicalMinorRecoveryCandidate
open NonprincipalReconstructionCandidate
variable {n m : ℕ}

def omittedGamma (T : Tournament n) (I J : Finset (Fin n)) : ℝ :=
  gamma (normalizedScore T)*(∏ i∈I,(1+normalizedScore T i)⁻¹)*
    (∏ j∈J,(1-normalizedScore T j)⁻¹)

lemma omittedGamma_nonneg (T : Tournament n) (I J : Finset (Fin n))
    (ha : ∀ i, |normalizedScore T i|<1) : 0≤omittedGamma T I J := by
  unfold omittedGamma
  rw [← retained_gamma (normalizedScore T) I J ha]
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i hi => by linarith [(abs_lt.mp (ha i)).1])
  · exact Finset.prod_nonneg (fun j hj => by linarith [(abs_lt.mp (ha j)).2])

lemma scalar_restoration_bound {n t v : ℝ} (m : ℕ)
    (hn : 1<n) (ht : 0≤t) (hm : (m:ℝ)=n-t) (hv : 0<n+v) :
    (((n-1)*(n+v))/n^2)^m≤Real.exp (-1+t/n+|v|) := by
  have hn0 : 0<n := by linarith
  have hleft : 0<1-1/n := by apply sub_pos.mpr; exact (div_lt_one hn0).mpr hn
  have hright : 0<1+v/n := by
    have hh : 0<(n+v)/n := div_pos hv hn0
    simpa only [add_div, div_self hn0.ne'] using hh
  have he : ((n-1)*(n+v))/n^2=(1-1/n)*(1+v/n) := by field_simp
  rw [he]
  have hp := mul_pos hleft hright
  rw [← Real.exp_log (pow_pos hp m), Real.log_pow,
    Real.log_mul hleft.ne' hright.ne']
  apply Real.exp_le_exp.mpr
  have hl := Real.log_le_sub_one_of_pos hleft
  have hr := Real.log_le_sub_one_of_pos hright
  have hs : Real.log (1-1/n)+Real.log (1+v/n)≤ -1/n+|v|/n := by
    have hh := div_le_div_of_nonneg_right (le_abs_self v) hn0.le
    simp only [neg_div] at hl hr hh ⊢
    linarith
  have hh := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg m)
  have hmn : (m:ℝ)≤n := by linarith
  have hvm : (m:ℝ)*(|v|/n)≤|v| := by
    calc
      _ ≤ n*(|v|/n) := mul_le_mul_of_nonneg_right hmn (by positivity)
      _ = _ := by field_simp
  have hconst : -(m:ℝ)/n= -1+t/n := by rw [hm]; field_simp; ring
  simp only [div_eq_mul_inv] at hh hvm hconst ⊢
  nlinarith only [hh,hvm,hconst]

lemma exact_recovery_scale (T : Tournament n) (I J : Finset (Fin n)) (hm : 0 < m) :
    recoveryFactor T I J m*base m=omittedGamma T I J*((m.factorial:ℝ)/(2:ℝ)^m)*
      ((((n:ℝ)-1)*((n:ℝ)+nu T))/(n:ℝ)^2)^m := by
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  have he : (m:ℝ)*((n:ℝ)-1)*((n:ℝ)+nu T)/(2*(n:ℝ)^2)=
      ((m:ℝ)/2)*((((n:ℝ)-1)*((n:ℝ)+nu T))/(n:ℝ)^2) := by ring
  unfold recoveryFactor base omittedGamma
  rw [he, mul_pow, div_pow]
  field_simp

lemma recovery_scale_upper (T : Tournament n) (I J : Finset (Fin n))
    (hn : 2≤n) (hm : 0 < m) (hdim : (m:ℝ)=(n:ℝ)-(I.card:ℝ))
    {a0 : ℝ} (h0 : 0≤a0) (h1 : a0<1) (ha : ∀ i,|normalizedScore T i|≤a0) :
    recoveryFactor T I J m*base m≤omittedGamma T I J*((m.factorial:ℝ)/(2:ℝ)^m)*
      Real.exp (-1+(I.card:ℝ)/(n:ℝ)+massBound T a0) := by
  rw [exact_recovery_scale T I J hm]
  apply mul_le_mul_of_nonneg_left
  · apply (scalar_restoration_bound m (by exact_mod_cast (show 1<n by omega))
      (Nat.cast_nonneg I.card) hdim (total_pos T hn h0 h1 ha)).trans
    exact Real.exp_le_exp.mpr (by linarith [nu_abs_bound T hn h0 h1 ha])
  · exact mul_nonneg (omittedGamma_nonneg T I J (fun i => (ha i).trans_lt h1)) (by positivity)
end GeneralScalarRestorationCandidate
