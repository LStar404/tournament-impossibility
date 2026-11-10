import ActualTournamentPrescalingBounds
import IndependentDeletionMass

/-! Actual total-mass normalization and its entry, marginal, Frobenius, and
independent-deletion consequences. No assumed marginal bounds, no assumed nu
smallness, and no extremality premise. -/
noncomputable section
namespace ActualPrescalingNormalization
open Finset TournamentHamiltonian TournamentPrescalingMass TournamentPrescalingMassBound
open ActualTournamentPrescalingBounds
variable {n : ℕ}

def nu (T : Tournament n) : ℝ := massExcess (signMatrix T) (normalizedScore T)
def massBound (T : Tournament n) (a0 : ℝ) : ℝ :=
  4*(radiusFactor a0)^2*errorScale n (tau (normalizedScore T))
def normalizer (T : Tournament n) : ℝ := (n:ℝ)/((n:ℝ)+nu T)
def normalizedMatrix (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => normalizer T*prescaled T i j

def normalizedMarginalBound (T : Tournament n) (a0 : ℝ) : ℝ :=
  16*(scaleCap a0)^2*Real.sqrt (tau (normalizedScore T))/Real.sqrt (n:ℝ)+
    4*massBound T a0/(n:ℝ)

/-- Exact bridge between the earlier nu and the actual pre-scaled matrix. -/
theorem prescaled_total (T : Tournament n) : ( ∑ i, ∑ j,prescaled T i j)=(n:ℝ)+nu T := by
  have he (i j : Fin n) : prescaled T i j=
      (ell (normalizedScore T) i*(1-(if i=j then 1 else 0)+signMatrix T i j)*
        rightScale (normalizedScore T) j)/((n:ℝ)-1) := by
    unfold prescaled scaled baseMatrix
    ring
  simp_rw [he,← sum_div]
  change rawMass (signMatrix T) (normalizedScore T)/((n:ℝ)-1)=
    (n:ℝ)+(rawMass (signMatrix T) (normalizedScore T)/((n:ℝ)-1)-(n:ℝ))
  ring

theorem prescaled_total_lower (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    (n:ℝ)/4 ≤ (n:ℝ)+nu T := by
  have h := sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ =>
    sum_le_sum (s := (univ : Finset (Fin n))) (fun j _ =>
    actual_entry_lower T hn h0 h1 ha i j))
  simp_rw [← sum_div] at h
  rw [base_total T hn,prescaled_total] at h
  exact h

lemma total_pos (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    0<(n:ℝ)+nu T := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  linarith [prescaled_total_lower T hn h0 h1 ha]

/-- Total normalization is safe without presuming |nu|<=n/2. -/
theorem normalizer_bounds (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    0<normalizer T  ∧  normalizer T ≤ 4 := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp := total_pos T hn h0 h1 ha
  constructor
  · exact div_pos (by linarith) hp
  · apply (div_le_iff₀ hp).mpr
    linarith [prescaled_total_lower T hn h0 h1 ha]

lemma nu_abs_bound (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    |nu T| ≤ massBound T a0 := by
  have h := actual_tournament_massExcess_bound T hn h0 h1 ha
  rw [← actual_tau_identity] at h
  exact h

lemma massBound_nonneg (T : Tournament n) (a0 : ℝ) : 0 ≤ massBound T a0 := by
  have ht := tau_nonneg (normalizedScore T)
  unfold massBound errorScale
  positivity

lemma normalizedMarginalBound_nonneg (T : Tournament n) (a0 : ℝ) :
    0 ≤ normalizedMarginalBound T a0 := by
  have hB := massBound_nonneg T a0
  unfold normalizedMarginalBound
  positivity

theorem normalizer_error_exact (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    normalizer T-1 = -nu T/((n:ℝ)+nu T) := by
  have hp := (total_pos T hn h0 h1 ha).ne'
  unfold normalizer
  field_simp [hp]; ring

theorem normalizer_error_bound (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    |normalizer T-1| ≤ 4*massBound T a0/(n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hp := total_pos T hn h0 h1 ha
  rw [normalizer_error_exact T hn h0 h1 ha,abs_div,abs_neg,abs_of_pos hp]
  calc
    _  ≤  massBound T a0/((n:ℝ)+nu T) :=
      div_le_div_of_nonneg_right (nu_abs_bound T hn h0 h1 ha) hp.le
    _ = normalizer T*(massBound T a0/(n:ℝ)) := by
      unfold normalizer
      field_simp [hn0.ne']
    _  ≤  4*(massBound T a0/(n:ℝ)) := mul_le_mul_of_nonneg_right
      (normalizer_bounds T hn h0 h1 ha).2 (div_nonneg (massBound_nonneg T a0) hn0.le)
    _ = _ := by ring

/-- Exactly n, not n plus an untracked residual. -/
theorem normalized_total (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    ( ∑ i, ∑ j,normalizedMatrix T i j)=(n:ℝ) := by
  simp only [normalizedMatrix,← mul_sum]
  rw [prescaled_total]
  exact div_mul_cancel₀ _ (total_pos T hn h0 h1 ha).ne'

theorem normalized_nonneg (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) (i j : Fin n) :
    0 ≤ normalizedMatrix T i j := by
  apply mul_nonneg (normalizer_bounds T hn h0 h1 ha).1.le
  exact (div_nonneg (base_nonneg T hn i j) (by norm_num)).trans
    (actual_entry_lower T hn h0 h1 ha i j)

theorem normalized_entry_bound (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) (i j : Fin n) :
    |normalizedMatrix T i j| ≤ 16*(scaleCap a0)^2/(n:ℝ) := by
  have hf := normalizer_bounds T hn h0 h1 ha
  rw [normalizedMatrix,abs_mul,abs_of_pos hf.1]
  have h := mul_le_mul hf.2 (actual_entry_bound T hn h0 h1 ha i j)
    (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
  convert h using 1; ring

lemma scaled_residual_bound {f x d e : ℝ} (hf0 : 0 ≤ f) (hf : f ≤ 4)
    (hx : |x-1| ≤ d) (he : |f-1| ≤ e) : |f*x-1| ≤ 4*d+e := by
  have hh : f*x-1=f*(x-1)+(f-1) := by ring
  rw [hh]
  calc
    _  ≤  |f*(x-1)|+|f-1| := abs_add_le _ _
    _  ≤  4*d+e := by
      rw [abs_mul,abs_of_nonneg hf0]
      exact add_le_add (mul_le_mul hf hx (abs_nonneg _) (by norm_num)) he

/-- Both normalized marginal errors are derived from actual pre-scaling and nu. -/
theorem normalized_marginals (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    ( ∀ i,|( ∑ j,normalizedMatrix T i j)-1| ≤ normalizedMarginalBound T a0)  ∧ 
    ( ∀ j,|( ∑ i,normalizedMatrix T i j)-1| ≤ normalizedMarginalBound T a0) := by
  have hf := normalizer_bounds T hn h0 h1 ha
  have hd := normalizer_error_bound T hn h0 h1 ha
  have hm := actual_marginals T hn h0 h1 ha
  constructor
  · intro i
    simp only [normalizedMatrix,← mul_sum]
    have h := scaled_residual_bound hf.1.le hf.2 (hm.1 i) hd
    convert h using 1; unfold normalizedMarginalBound; ring
  · intro j
    simp only [normalizedMatrix,← mul_sum]
    have h := scaled_residual_bound hf.1.le hf.2 (hm.2 j) hd
    convert h using 1; unfold normalizedMarginalBound; ring

lemma prescaled_frobenius_le (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    ( ∑ i, ∑ j,(prescaled T i j)^2) ≤ 16*(scaleCap a0)^4 := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hne : (n:ℝ)≠0 := by linarith
  have hp (i j : Fin n) : (prescaled T i j)^2 ≤ (4*(scaleCap a0)^2/(n:ℝ))^2 := by
    have h := mul_self_le_mul_self (abs_nonneg (prescaled T i j))
      (actual_entry_bound T hn h0 h1 ha i j)
    simpa [← pow_two,sq_abs] using h
  calc
    _  ≤   ∑ i : Fin n, ∑ j : Fin n,(4*(scaleCap a0)^2/(n:ℝ))^2 :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hp i j))
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp [hne]; ring

/-- Quantitative cost of total-mass normalization itself. -/
theorem normalization_frobenius_bound (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    ( ∑ i, ∑ j,(normalizedMatrix T i j-prescaled T i j)^2) ≤ 
      256*(scaleCap a0)^4*(massBound T a0)^2/(n:ℝ)^2 := by
  have he (i j : Fin n) : (normalizedMatrix T i j-prescaled T i j)^2=
      (normalizer T-1)^2*(prescaled T i j)^2 := by unfold normalizedMatrix; ring
  simp_rw [he,← mul_sum]
  have hs := mul_self_le_mul_self (abs_nonneg (normalizer T-1))
    (normalizer_error_bound T hn h0 h1 ha)
  simp only [← pow_two,sq_abs] at hs
  have h := mul_le_mul hs (prescaled_frobenius_le T hn h0 h1 ha)
    (sum_nonneg (fun i _ => sum_nonneg (fun j _ => sq_nonneg _)))
    (sq_nonneg (4*massBound T a0/(n:ℝ)))
  convert h using 1; ring

/-- Combined displacement from the original normalized tournament matrix. -/
theorem normalized_frobenius_bound (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    ( ∑ i, ∑ j,(normalizedMatrix T i j-baseMatrix T i j)^2) ≤ 
      128*(scaleCap a0)^4*tau (normalizedScore T)/(n:ℝ)+
        512*(scaleCap a0)^4*(massBound T a0)^2/(n:ℝ)^2 := by
  have hp (i j : Fin n) : (normalizedMatrix T i j-baseMatrix T i j)^2 ≤ 
      2*(normalizedMatrix T i j-prescaled T i j)^2+
        2*(prescaled T i j-baseMatrix T i j)^2 := by
    nlinarith [sq_nonneg (normalizedMatrix T i j-2*prescaled T i j+baseMatrix T i j)]
  have h := sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ =>
    sum_le_sum (s := (univ : Finset (Fin n))) (fun j _ => hp i j))
  simp only [sum_add_distrib,← mul_sum] at h
  have hN := normalization_frobenius_bound T hn h0 h1 ha
  have hP := actual_frobenius_bound T hn h0 h1 ha
  calc
    _ ≤ 2*(256*(scaleCap a0)^4*(massBound T a0)^2/(n:ℝ)^2)+
        2*(64*(scaleCap a0)^4*tau (normalizedScore T)/(n:ℝ)) := by
      linarith only [h, hN, hP]
    _ = _ := by ring

/-- Actual G1 independent-deletion bound. No mass, entry, or marginal premise
is left to the caller: all are discharged for the actual normalized matrix. -/
theorem actual_independent_deletion_bound (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0)
    (I J : Finset (Fin n)) (hcard : J.card=I.card) (hhalf : 2*I.card ≤ n) :
    |IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J| ≤ 
      4*(I.card:ℝ)*normalizedMarginalBound T a0+
        2*(16*(scaleCap a0)^2+1)*(I.card:ℝ)^2/(n:ℝ) := by
  have hm := normalized_marginals T hn h0 h1 ha
  exact IndependentDeletionMass.deletionExcess_bound (normalizedMatrix T) I J
    (normalized_total T hn h0 h1 ha) hcard (by omega) hhalf (by positivity)
    (normalizedMarginalBound_nonneg T a0) (normalized_entry_bound T hn h0 h1 ha)
    hm.1 hm.2

end ActualPrescalingNormalization
#print axioms ActualPrescalingNormalization.prescaled_total
#print axioms ActualPrescalingNormalization.normalizer_bounds
#print axioms ActualPrescalingNormalization.normalizer_error_bound
#print axioms ActualPrescalingNormalization.normalized_total
#print axioms ActualPrescalingNormalization.normalized_marginals
#print axioms ActualPrescalingNormalization.normalized_frobenius_bound
#print axioms ActualPrescalingNormalization.actual_independent_deletion_bound
