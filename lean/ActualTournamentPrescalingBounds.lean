import TournamentPrescalingMassBound

/-! Actual pre-scaled tournament matrices: entries, marginals, and Frobenius
squared displacement. No marginal-error or energy-window conclusion is assumed. All constants are explicit in the fixed cap a0<1. -/
noncomputable section
namespace ActualTournamentPrescalingBounds
open Finset TournamentPrescalingMass TournamentPrescalingMassBound
open TournamentHamiltonian
variable {n : ℕ}

def scaleCap (a0 : ℝ) : ℝ := (1-a0)⁻¹

def normalizedScore (T : Tournament n) (i : Fin n) : ℝ := score T i / ((n : ℝ)-1)

def baseMatrix (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (1 - (if i=j then 1 else 0) + signMatrix T i j) / ((n : ℝ)-1)

def scaled (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ell a i * C i j * rightScale a j

def prescaled (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  scaled (baseMatrix T) (normalizedScore T)

def marginalBound (n : ℕ) (a0 t : ℝ) : ℝ :=
  2*(scaleCap a0)^2*Real.sqrt (n : ℝ)*Real.sqrt t/((n : ℝ)-1)

lemma scaleCap_pos {a0 : ℝ} (h1 : a0<1) : 0<scaleCap a0 :=
  inv_pos.mpr (sub_pos.mpr h1)

lemma one_le_scaleCap {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0<1) : 1 ≤ scaleCap a0 :=
  (one_le_inv₀ (sub_pos.mpr h1)).mpr (by linarith)

lemma one_add_positive {x a0 : ℝ} (h1 : a0<1) (hx : |x| ≤ a0) : 0<1+x := by
  have h := neg_le_abs x
  linarith

/-- Both scale factors and their differences from one are controlled directly. -/
lemma scalar_inverse_bounds {x a0 : ℝ} (_h0 : 0 ≤ a0) (h1 : a0<1) (hx : |x| ≤ a0) :
    (1/2 : ℝ)  ≤  (1+x)⁻¹  ∧  (1+x)⁻¹  ≤  scaleCap a0  ∧ 
      |(1+x)⁻¹-1|  ≤  scaleCap a0*|x| := by
  have hp := one_add_positive h1 hx
  have hu : 1+x ≤ 2 := by linarith [le_abs_self x]
  have hl : 1-a0 ≤ 1+x := by linarith [neg_le_abs x]
  have hb : (1+x)⁻¹ ≤ scaleCap a0 :=
    (inv_le_inv₀ hp (sub_pos.mpr h1)).mpr hl
  refine ⟨?_,hb,?_⟩
  · simpa using (inv_le_inv₀ (by norm_num : (0:ℝ)<2) hp).mpr hu
  · have he : (1+x)⁻¹-1 = -x/(1+x) := by field_simp [hp.ne']; ring
    rw [he,abs_div,abs_neg,abs_of_pos hp,div_eq_mul_inv]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hb (abs_nonneg x)

lemma ell_bounds (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|a i| ≤ a0) (i : Fin n) :
    (1/2 : ℝ) ≤ ell a i  ∧  ell a i ≤ scaleCap a0  ∧  |ell a i-1| ≤ scaleCap a0*|a i| :=
  scalar_inverse_bounds h0 h1 (ha i)

lemma right_bounds (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|a i| ≤ a0) (i : Fin n) :
    (1/2 : ℝ) ≤ rightScale a i  ∧  rightScale a i ≤ scaleCap a0  ∧ 
      |rightScale a i-1| ≤ scaleCap a0*|a i| := by
  simpa [rightScale,sub_eq_add_neg] using
    scalar_inverse_bounds h0 h1 (show |-a i| ≤ a0 by simpa using ha i)

lemma score_sum_zero (T : Tournament n) :  ∑ i,normalizedScore T i=0 := by
  unfold normalizedScore
  rw [← sum_div,TournamentHamiltonian.score_sum_zero,zero_div]

lemma base_eq_adjacency (T : Tournament n) (i j : Fin n) :
    baseMatrix T i j = (2*adjacency T i j)/((n : ℝ)-1) := by
  rw [baseMatrix,← twice_adjacency]

lemma base_nonneg (T : Tournament n) (hn : 2 ≤ n) (i j : Fin n) : 0 ≤ baseMatrix T i j := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  rw [base_eq_adjacency]
  exact div_nonneg (mul_nonneg (by norm_num) (adjacency_nonneg T i j)) (by linarith)

lemma base_entry_bound (T : Tournament n) (hn : 2 ≤ n) (i j : Fin n) :
    |baseMatrix T i j| ≤ 2/((n : ℝ)-1) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hu : adjacency T i j ≤ 1 := by cases h:T.val i j <;> simp [adjacency,h]
  rw [abs_of_nonneg (base_nonneg T hn i j),base_eq_adjacency]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma base_row (T : Tournament n) (hn : 2 ≤ n) (i : Fin n) :
    ( ∑ j,baseMatrix T i j)=1+normalizedScore T i := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hne : (n:ℝ)-1≠0 := by linarith
  have hnum : ( ∑ j, (1 -(if i=j then (1:ℝ) else 0)+signMatrix T i j))=
      (n:ℝ)-1+score T i := by
    simp [sum_add_distrib,sum_sub_distrib,score]
  unfold baseMatrix normalizedScore
  rw [← sum_div,hnum]
  field_simp [hne]

lemma base_col (T : Tournament n) (hn : 2 ≤ n) (j : Fin n) :
    ( ∑ i,baseMatrix T i j)=1-normalizedScore T j := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hne : (n:ℝ)-1≠0 := by linarith
  have hs : ( ∑ i,signMatrix T i j)=-score T j := by
    calc
      _ =  ∑ i,-signMatrix T j i := sum_congr rfl (fun i _ => signMatrix_skew T i j)
      _ = _ := by simp [score]
  have hnum : ( ∑ i, (1 -(if i=j then (1:ℝ) else 0)+signMatrix T i j))=
      (n:ℝ)-1-score T j := by
    simp only [sum_add_distrib,sum_sub_distrib]
    rw [hs]
    simp
    ring
  unfold baseMatrix normalizedScore
  rw [← sum_div,hnum]
  field_simp [hne]

lemma base_total (T : Tournament n) (hn : 2 ≤ n) : ( ∑ i, ∑ j,baseMatrix T i j)=(n:ℝ) := by
  simp_rw [base_row T hn]
  rw [sum_add_distrib,score_sum_zero]
  simp

lemma sum_abs_score_le (a : Fin n → ℝ) :
    ( ∑ i,|a i|) ≤ Real.sqrt (n:ℝ)*Real.sqrt (tau a) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin n))
    (fun _ => (1:ℝ)) (fun i => |a i|)
  simpa [tau,sq_abs] using h

lemma scaled_row_residual (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hrow :  ∀ i,( ∑ j,C i j)=1+a i) (ha :  ∀ i,|a i|<1) (i : Fin n) :
    ( ∑ j,scaled C a i j)-1 = ell a i*( ∑ j,C i j*(rightScale a j-1)) := by
  have hp : 1+a i≠0 := by have h := abs_lt.mp (ha i); linarith
  have he : ell a i*( ∑ j,C i j)=1 := by rw [hrow]; exact inv_mul_cancel₀ hp
  have hs : ( ∑ j,scaled C a i j)=ell a i*( ∑ j,C i j*rightScale a j) := by
    simp [scaled,mul_sum,mul_assoc]
  rw [hs]
  simp only [mul_sub,sum_sub_distrib,mul_one]
  linarith

/-- Marginal bound derived from original entries and the exact score equation. -/
theorem scaled_row_bound (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hn : 2 ≤ n) {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|a i| ≤ a0)
    (hrow :  ∀ i,( ∑ j,C i j)=1+a i)
    (hentry :  ∀ i j,|C i j| ≤ 2/((n:ℝ)-1)) (i : Fin n) :
    |( ∑ j,scaled C a i j)-1| ≤ marginalBound n a0 (tau a) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hc : 0 ≤ 2/((n:ℝ)-1) := div_nonneg (by norm_num) (by linarith)
  have hb := ell_bounds a h0 h1 ha i
  have hl0 : 0 ≤ ell a i := by linarith [hb.1]
  have hL : 0 ≤ scaleCap a0 := (scaleCap_pos h1).le
  have hinner : |(∑ j, C i j*(rightScale a j-1))| ≤ 
      (2/((n:ℝ)-1))*scaleCap a0*( ∑ j,|a j|) := by
    calc
      _  ≤   ∑ j,|C i j*(rightScale a j-1)| := abs_sum_le_sum_abs _ _
      _  ≤   ∑ j,(2/((n:ℝ)-1))*(scaleCap a0*|a j|) := by
        apply sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul (hentry i j) (right_bounds a h0 h1 ha j).2.2 (abs_nonneg _) hc
      _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro j hj; ring
  rw [scaled_row_residual C a hrow (fun j => (ha j).trans_lt h1),abs_mul,
    abs_of_nonneg hl0]
  calc
    _  ≤  scaleCap a0*((2/((n:ℝ)-1))*scaleCap a0*( ∑ j,|a j|)) :=
      mul_le_mul hb.2.1 hinner (abs_nonneg _) hL
    _  ≤  scaleCap a0*((2/((n:ℝ)-1))*scaleCap a0*
        (Real.sqrt (n:ℝ)*Real.sqrt (tau a))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_abs_score_le a) (mul_nonneg hc hL)) hL
    _ = _ := by unfold marginalBound; ring

lemma scaled_transpose (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    (scaled C a).transpose=scaled C.transpose (-a) := by
  ext i j
  simp [Matrix.transpose_apply,scaled,ell,rightScale,sub_eq_add_neg,
    mul_comm,mul_left_comm,mul_assoc]

lemma tau_neg (a : Fin n → ℝ) : tau (-a)=tau a := by simp [tau]

theorem scaled_col_bound (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hn : 2 ≤ n) {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|a i| ≤ a0)
    (hcol :  ∀ j,( ∑ i,C i j)=1-a j)
    (hentry :  ∀ i j,|C i j| ≤ 2/((n:ℝ)-1)) (j : Fin n) :
    |( ∑ i,scaled C a i j)-1| ≤ marginalBound n a0 (tau a) := by
  have h := scaled_row_bound C.transpose (-a) hn h0 h1
    (fun i => by simpa using ha i) (fun i => by simpa [sub_eq_add_neg] using hcol i)
    (fun i j => hentry j i) j
  rw [← scaled_transpose,tau_neg] at h
  exact h

lemma two_over_pred_le (hn : 2 ≤ n) : (2:ℝ)/((n:ℝ)-1) ≤ 4/(n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  linarith

lemma marginalBound_le (hn : 2 ≤ n) (a0 : ℝ) {t : ℝ} (_ht : 0 ≤ t) :
    marginalBound n a0 t ≤ 4*(scaleCap a0)^2*Real.sqrt t/Real.sqrt (n:ℝ) := by
  have hm := mul_le_mul_of_nonneg_right (two_over_pred_le hn)
    (show 0 ≤ (scaleCap a0)^2*Real.sqrt (n:ℝ)*Real.sqrt t by positivity)
  calc
    _  ≤  (4/(n:ℝ))*((scaleCap a0)^2*Real.sqrt (n:ℝ)*Real.sqrt t) := by
      convert hm using 1; unfold marginalBound; ring
    _ = 4*(scaleCap a0)^2*Real.sqrt t*(Real.sqrt (n:ℝ)/(n:ℝ)) := by ring
    _ = _ := by rw [Real.sqrt_div_self']; ring

/-- Actual row and column errors, with no presumed marginal bounds. -/
theorem actual_marginals (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    ( ∀ i,|( ∑ j,prescaled T i j)-1| ≤ 4*(scaleCap a0)^2*
      Real.sqrt (tau (normalizedScore T))/Real.sqrt (n:ℝ))  ∧ 
    ( ∀ j,|( ∑ i,prescaled T i j)-1| ≤ 4*(scaleCap a0)^2*
      Real.sqrt (tau (normalizedScore T))/Real.sqrt (n:ℝ)) := by
  constructor
  · intro i
    exact (scaled_row_bound _ _ hn h0 h1 ha (base_row T hn) (base_entry_bound T hn) i).trans
      (marginalBound_le hn a0 (tau_nonneg _))
  · intro j
    exact (scaled_col_bound _ _ hn h0 h1 ha (base_col T hn) (base_entry_bound T hn) j).trans
      (marginalBound_le hn a0 (tau_nonneg _))

lemma scaled_entry_abs (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    {a0 K : ℝ} (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|a i| ≤ a0)
    (hK : 0 ≤ K) (hentry :  ∀ i j,|C i j| ≤ K) (i j : Fin n) :
    |scaled C a i j| ≤ (scaleCap a0)^2*K := by
  have hl := ell_bounds a h0 h1 ha i
  have hr := right_bounds a h0 h1 ha j
  have hl0 : 0 ≤ ell a i := by linarith [hl.1]
  have hr0 : 0 ≤ rightScale a j := by linarith [hr.1]
  rw [scaled,abs_mul,abs_mul,abs_of_nonneg hl0,abs_of_nonneg hr0]
  calc
    _  ≤  (scaleCap a0*K)*scaleCap a0 :=
      mul_le_mul (mul_le_mul hl.2.1 (hentry i j) (abs_nonneg _) (scaleCap_pos h1).le)
        hr.2.1 hr0 (mul_nonneg (scaleCap_pos h1).le hK)
    _ = _ := by ring

theorem actual_entry_bound (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) (i j : Fin n) :
    |prescaled T i j| ≤ 4*(scaleCap a0)^2/(n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpred : 0<(n:ℝ)-1 := by linarith
  have h := scaled_entry_abs (baseMatrix T) (normalizedScore T) h0 h1 ha
    (show 0 ≤ 2/((n:ℝ)-1) by positivity) (base_entry_bound T hn) i j
  have hh := mul_le_mul_of_nonneg_left (two_over_pred_le hn) (sq_nonneg (scaleCap a0))
  exact h.trans (by convert hh using 1; ring)

/-- Uniform positivity of both scale factors is used later to normalize total
mass without assuming the desired smallness of nu. -/
theorem actual_entry_lower (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) (i j : Fin n) :
    baseMatrix T i j/4 ≤ prescaled T i j := by
  have hl := (ell_bounds (normalizedScore T) h0 h1 ha i).1
  have hr := (right_bounds (normalizedScore T) h0 h1 ha j).1
  have hc := base_nonneg T hn i j
  have hp := mul_le_mul (mul_le_mul_of_nonneg_right hl hc) hr
    (by norm_num : (0:ℝ) ≤ 1/2) (by nlinarith)
  change _ ≤ ell (normalizedScore T) i*baseMatrix T i j*rightScale (normalizedScore T) j
  convert hp using 1; ring

lemma scale_product_error (a : Fin n → ℝ) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|a i| ≤ a0) (i j : Fin n) :
    |ell a i*rightScale a j-1| ≤ (scaleCap a0)^2*(|a i|+|a j|) := by
  have hl := ell_bounds a h0 h1 ha i
  have hr := right_bounds a h0 h1 ha j
  have hL := (scaleCap_pos h1).le
  have he : ell a i*rightScale a j-1=(ell a i-1)*rightScale a j+(rightScale a j-1) := by ring
  rw [he]
  calc
    _  ≤  |(ell a i-1)*rightScale a j|+|rightScale a j-1| := abs_add_le _ _
    _  ≤  (scaleCap a0*|a i|)*scaleCap a0+scaleCap a0*|a j| := by
      rw [abs_mul,abs_of_nonneg (show 0 ≤ rightScale a j by linarith [hr.1])]
      exact add_le_add (mul_le_mul hl.2.2 hr.2.1
        (by linarith [hr.1]) (mul_nonneg hL (abs_nonneg _))) hr.2.2
    _  ≤  (scaleCap a0*|a i|)*scaleCap a0+(scaleCap a0)^2*|a j| := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      nlinarith [one_le_scaleCap h0 h1]
    _ = _ := by ring

lemma scaled_difference_abs (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    {a0 K : ℝ} (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|a i| ≤ a0)
    (hK : 0 ≤ K) (hentry :  ∀ i j,|C i j| ≤ K) (i j : Fin n) :
    |scaled C a i j-C i j| ≤ K*(scaleCap a0)^2*(|a i|+|a j|) := by
  have he : scaled C a i j-C i j=C i j*(ell a i*rightScale a j-1) := by unfold scaled; ring
  rw [he,abs_mul]
  have h := mul_le_mul (hentry i j) (scale_product_error a h0 h1 ha i j) (abs_nonneg _) hK
  convert h using 1; ring

lemma two_index_energy (a : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, ((a i)^2+(a j)^2))=2*(n:ℝ)*tau a := by
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_sum]
  unfold tau
  ring

/-- Frobenius squared displacement, derived entrywise for the actual matrix. -/
theorem actual_frobenius_exact (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    ( ∑ i, ∑ j,(prescaled T i j-baseMatrix T i j)^2) ≤ 
      16*(scaleCap a0)^4*(n:ℝ)*tau (normalizedScore T)/((n:ℝ)-1)^2 := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpred : 0<(n:ℝ)-1 := by linarith
  have hK : 0 ≤ 2/((n:ℝ)-1) := by positivity
  have hp (i j : Fin n) : (prescaled T i j-baseMatrix T i j)^2 ≤ 
      (8*(scaleCap a0)^4/((n:ℝ)-1)^2)*
        ((normalizedScore T i)^2+(normalizedScore T j)^2) := by
    have h := scaled_difference_abs _ _ h0 h1 ha hK (base_entry_bound T hn) i j
    have hs := mul_self_le_mul_self (abs_nonneg (prescaled T i j-baseMatrix T i j)) h
    have ha2 : (|normalizedScore T i|+|normalizedScore T j|)^2 ≤ 
        2*((normalizedScore T i)^2+(normalizedScore T j)^2) := by
      nlinarith [sq_nonneg (|normalizedScore T i|-|normalizedScore T j|),
        sq_abs (normalizedScore T i),sq_abs (normalizedScore T j)]
    have hm := mul_le_mul_of_nonneg_left ha2
      (sq_nonneg ((2/((n:ℝ)-1))*(scaleCap a0)^2))
    calc
      _  ≤  ((2/((n:ℝ)-1))*(scaleCap a0)^2)^2*
          (|normalizedScore T i|+|normalizedScore T j|)^2 := by
        convert hs using 1 <;> simp only [← pow_two,sq_abs]; ring
      _  ≤  ((2/((n:ℝ)-1))*(scaleCap a0)^2)^2*
          (2*((normalizedScore T i)^2+(normalizedScore T j)^2)) := hm
      _ = _ := by field_simp [hpred.ne']; ring
  calc
    _  ≤   ∑ i, ∑ j,(8*(scaleCap a0)^4/((n:ℝ)-1)^2)*
        ((normalizedScore T i)^2+(normalizedScore T j)^2) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hp i j))
    _ = _ := by
      simp_rw [← mul_sum]
      rw [two_index_energy]
      ring

theorem actual_frobenius_bound (T : Tournament n) (hn : 2 ≤ n) {a0 : ℝ}
    (h0 : 0 ≤ a0) (h1 : a0<1) (ha :  ∀ i,|normalizedScore T i| ≤ a0) :
    ( ∑ i, ∑ j,(prescaled T i j-baseMatrix T i j)^2) ≤ 
      64*(scaleCap a0)^4*tau (normalizedScore T)/(n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0<((n:ℝ)-1)^2 := sq_pos_of_pos (by linarith)
  have ht := tau_nonneg (normalizedScore T)
  have hs : (n:ℝ)^2 ≤ 4*((n:ℝ)-1)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 16*(scaleCap a0)^4*tau (normalizedScore T) by positivity)
  apply (actual_frobenius_exact T hn h0 h1 ha).trans
  apply (div_le_div_iff₀ hp (by linarith)).mpr
  nlinarith

end ActualTournamentPrescalingBounds
#print axioms ActualTournamentPrescalingBounds.base_total
#print axioms ActualTournamentPrescalingBounds.actual_marginals
#print axioms ActualTournamentPrescalingBounds.actual_entry_bound
#print axioms ActualTournamentPrescalingBounds.actual_entry_lower
#print axioms ActualTournamentPrescalingBounds.actual_frobenius_bound
