import PermanentCircleActualCentering
import PermanentCircleExceptional
import PermanentCircleRootSum
import PermanentHomogeneousEnvelope

/-! Verified in the 557-module direct-Lean compilation and declaration audit.
A genuine permanent circle envelope.
All hypotheses concern entries, scores and the Euclidean norm of M. -/
noncomputable section
namespace PermanentSpectralFrame
open Matrix
variable {n : ℕ}

lemma singular_root_le_operator_bound (A : Matrix (Fin n) (Fin n) ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hA : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) A‖ ≤ L)
    (i : Fin n) : singularRoot A i ≤ L := by
  classical
  have h := matrix_operator_energy A L hL hA
    ((frame A : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1)
  rw [image_frame_energy, frame_energy] at h
  have he : eigenvalue A i ≤ L ^ 2 := by simpa [Pi.single_apply, apply_ite, mul_ite] using h
  exact (Real.sqrt_le_left hL).mpr he

lemma actual_circle_entry_bound (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {C T : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hz : ‖z‖ ≤ T)
    (hentry : ∀ i j, ‖M i j‖ ≤ C / n) (i j : Fin n) :
    ‖(averaging n + z • M) i j‖ ≤ (1 + T * C) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change ‖(n : ℂ)⁻¹ + z * M i j‖ ≤ _
  calc
    _ ≤ ‖(n : ℂ)⁻¹‖ + ‖z * M i j‖ := norm_add_le _ _
    _ = (n : ℝ)⁻¹ + ‖z‖ * ‖M i j‖ := by simp [norm_mul]
    _ ≤ (n : ℝ)⁻¹ + T * (C / n) :=
      add_le_add le_rfl (mul_le_mul hz (hentry i j) (norm_nonneg _) hT)
    _ = (1 + T * C) / n := by ring

lemma actual_circle_exceptional_root (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {T q : ℝ}
    (hT : 0 ≤ T) (hq : 0 ≤ q) (hz : ‖z‖ ≤ T)
    (hM : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) M‖ ≤ q) :
    ∃ i0 : Fin n, ∀ i, i ≠ i0 → singularRoot (averaging n + z • M) i ≤ T * q := by
  have hE : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (z • M)‖ ≤ T * q := by
    rw [map_smul, norm_smul]
    exact mul_le_mul hz hM (norm_nonneg _) hT
  simpa only [← averaging_rankOne] using
    exists_exceptional_root hn (fun _ => (1 : ℂ)) (fun _ => (n : ℂ)⁻¹)
      (z • M) (T * q) (mul_nonneg hT hq) hE

lemma small_increment_power_le_exp (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a) :
    (1 + a / n) ^ n ≤ Real.exp a := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (Real.exp (a / n)) ^ n := pow_le_pow_left₀ (by positivity)
      (by simpa only [add_comm] using Real.add_one_le_exp (a / n)) n
    _ = Real.exp a := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [ne_of_gt hnR]

/-- The actual finite permanent has a subexponential circle envelope.
No permanent bound, root ordering or auxiliary moment premise is assumed. -/
theorem actual_permanent_circle_envelope (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {K C T q : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hrow : ∀ i, ‖∑ j, M i j‖ ≤ K / n)
    (hcol : ∀ j, ‖∑ i, M i j‖ ≤ K / n)
    (hentry : ∀ i j, ‖M i j‖ ≤ C / n)
    (hz : ‖z‖ ≤ T) (hM : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) M‖ ≤ q)
    (hTq : T * q < 1) :
    ‖Matrix.permanent (averaging n + z • M)‖ ≤
      ((n.factorial : ℝ) / (n : ℝ)^n) *
      Real.exp (2*T*K + (1+T*C)*Real.sqrt (n : ℝ)/(1-T*q)) := by
  classical
  let A := averaging n + z • M
  let L : ℝ := 1 + 2*T*K/n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 1 ≤ L := by
    have hnonneg : 0 ≤ 2*T*K/(n : ℝ) := by positivity
    dsimp [L]
    linarith
  obtain ⟨i0, hi0⟩ := actual_circle_exceptional_root hn M z hT hq hz hM
  have htop : singularRoot A i0 ≤ L :=
    singular_root_le_operator_bound A L (zero_le_one.trans hL)
      (actual_circle_operator_bound hn M z hK hT hq hrow hcol hz hM hTq.le) i0
  have hp := PermanentPositiveMoments.spectral_permanent_exceptional_exp_bound hn A i0
    hL htop hi0 hTq
  have hs : (∑ i ∈ Finset.univ.erase i0, singularRoot A i) ≤
      (1+T*C)*Real.sqrt (n : ℝ) :=
    singular_root_erase_sum_le_of_entry hn A (1+T*C) (by positivity)
      (actual_circle_entry_bound hn M z hC hT hz hentry) i0
  have hpow : L^n ≤ Real.exp (2*T*K) :=
    small_increment_power_le_exp hn (2*T*K) (by positivity)
  have hexp : Real.exp ((∑ i ∈ Finset.univ.erase i0, singularRoot A i)/(1-T*q)) ≤
      Real.exp ((1+T*C)*Real.sqrt (n : ℝ)/(1-T*q)) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hs (sub_pos.mpr hTq).le)
  have hc : 0 ≤ (n.factorial : ℝ)/(n : ℝ)^n := by positivity
  calc
    _ ≤ ((n.factorial : ℝ)/(n : ℝ)^n)*L^n*
        Real.exp ((∑ i ∈ Finset.univ.erase i0, singularRoot A i)/(1-T*q)) := hp
    _ ≤ ((n.factorial : ℝ)/(n : ℝ)^n)*Real.exp (2*T*K)*
        Real.exp ((1+T*C)*Real.sqrt (n : ℝ)/(1-T*q)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow hc) hexp
        (Real.exp_pos _).le (mul_nonneg hc (Real.exp_pos _).le)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]

/-- Normalization by n!/n^n gives the requested dimension-uniform envelope. -/
theorem normalized_permanent_circle_envelope (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {K C T q : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hrow : ∀ i, ‖∑ j, M i j‖ ≤ K / n)
    (hcol : ∀ j, ‖∑ i, M i j‖ ≤ K / n)
    (hentry : ∀ i j, ‖M i j‖ ≤ C / n)
    (hz : ‖z‖ ≤ T) (hM : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) M‖ ≤ q)
    (hTq : T*q < 1) :
    ‖Matrix.permanent (averaging n + z • M)‖ / ((n.factorial : ℝ)/(n : ℝ)^n) ≤
      Real.exp (2*T*K+(1+T*C)*Real.sqrt (n : ℝ)/(1-T*q)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity : 0 < (n.factorial : ℝ)/(n : ℝ)^n)).mpr
  simpa only [mul_comm] using
    actual_permanent_circle_envelope hn M z hK hC hT hq hrow hcol hentry hz hM hTq
end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.actual_permanent_circle_envelope
#print axioms PermanentSpectralFrame.normalized_permanent_circle_envelope
