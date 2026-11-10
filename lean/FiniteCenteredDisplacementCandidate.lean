import NormalizationScalarsCandidate
import RealBilinearTrace
import SameRootFrobeniusCandidate
/-! Isolated verified (2026-11-10). Actual finite normalization/centering algebra, with
explicit base-matrix identity and supplied same controlled scaling witness. -/
set_option autoImplicit false
noncomputable section
namespace FiniteCenteredDisplacementCandidate
open Matrix Finset RealBilinearTrace RealGramEndpoint
open ActualHessianFinite MatrixScalingMassPotential ActualReconstructionBridgeCandidate
variable {n m : ℕ}
def constant (m : ℕ) (a : ℝ) : Matrix (Fin m) (Fin m) ℝ := fun _ _ => a
def center (D : Matrix (Fin m) (Fin m) ℝ) := (1-P m)*D*(1-P m)
lemma center_constant (hm : 0 < m) (a : ℝ) : center (constant m a)=0 := by
  have hp : P m*constant m a=constant m a := by
    ext i j
    simp only [Matrix.mul_apply, P, constant, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    field_simp
  unfold center
  rw [Matrix.sub_mul, Matrix.one_mul, hp, sub_self, Matrix.zero_mul]
lemma center_add (D E : Matrix (Fin m) (Fin m) ℝ) : center (D+E)=center D+center E := by
  unfold center
  rw [Matrix.mul_add, Matrix.add_mul]
lemma center_sub (D E : Matrix (Fin m) (Fin m) ℝ) : center (D-E)=center D-center E := by
  unfold center
  noncomm_ring
lemma center_smul (a : ℝ) (D : Matrix (Fin m) (Fin m) ℝ) : center (a • D)=a • center D := by
  unfold center
  rw [Matrix.mul_smul, Matrix.smul_mul]
lemma center_fnorm (hm : 0 < m) (D : Matrix (Fin m) (Fin m) ℝ) : fnorm (center D) ≤ fnorm D := by
  rw [← sqrt_frob, ← sqrt_frob]
  apply Real.sqrt_le_sqrt
  exact SameRootFrobeniusCandidate.centered_sqF_contraction hm D
lemma restriction_frob (D : Matrix (Fin n) (Fin n) ℝ) (e f : Fin m ↪ Fin n) :
    frob (D.submatrix e f) ≤ frob D := by
  have sum_restrict (g : Fin n → ℝ) (hg : ∀ i, 0 ≤ g i) (e : Fin m ↪ Fin n) :
      ∑ i, g (e i) ≤ ∑ i, g i := by
    calc
      _ = ∑ i ∈ Finset.univ.image e, g i := by rw [Finset.sum_image]; intro a ha b hb hab; exact e.injective hab
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hg i)
  unfold frob
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin n, D (e i) j ^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact sum_restrict (fun j => D (e i) j^2) (fun j => sq_nonneg _) f
    _ ≤ _ := sum_restrict (fun i => ∑ j, D i j^2) (fun i => Finset.sum_nonneg fun j _ => sq_nonneg _) e
lemma restriction_fnorm (D : Matrix (Fin n) (Fin n) ℝ) (e f : Fin m ↪ Fin n) :
    fnorm (D.submatrix e f) ≤ fnorm D := by
  rw [← sqrt_frob, ← sqrt_frob]
  exact Real.sqrt_le_sqrt (restriction_frob D e f)
/-- Base relation C0=Z+constant is the exact actual tournament identity,
kept explicit here. e,f may be different. beta is not replaced by n/m. -/
lemma centered_identity (hm : 0 < m) (A C0 Z : Matrix (Fin n) (Fin n) ℝ)
    (e f : Fin m ↪ Fin n) (a beta : ℝ) (hC : C0=Z+constant n a) :
    center (beta • A.submatrix e f)-center (Z.submatrix e f) =
      center (beta • ((A-C0).submatrix e f)+(beta-1) • Z.submatrix e f) := by
  have he : beta • A.submatrix e f-Z.submatrix e f =
      beta • ((A-C0).submatrix e f)+(beta-1) • Z.submatrix e f+beta • constant m a := by
    rw [hC]
    ext i j
    simp [Matrix.submatrix, constant, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring
  rw [← center_sub, he, center_add, center_smul, center_constant hm a, smul_zero, add_zero]
lemma centered_displacement (hm : 0 < m) (A C0 Z : Matrix (Fin n) (Fin n) ℝ)
    (e f : Fin m ↪ Fin n) (a beta b : ℝ) (hC : C0=Z+constant n a)
    (hb0 : 0 ≤ beta) (hb : beta ≤ 2) (he : |beta-1| ≤ b)
    (hZ : fnorm Z ≤ 2) :
    fnorm (center (beta • A.submatrix e f)-center (Z.submatrix e f)) ≤
      2*fnorm (A-C0)+2*b := by
  have hbnon : 0 ≤ b := (abs_nonneg _).trans he
  rw [centered_identity hm A C0 Z e f a beta hC]
  calc
    _ ≤ fnorm (beta • ((A-C0).submatrix e f)+(beta-1) • Z.submatrix e f) := center_fnorm hm _
    _ ≤ fnorm (beta • ((A-C0).submatrix e f))+fnorm ((beta-1) • Z.submatrix e f) := fnorm_add _ _
    _ = beta*fnorm ((A-C0).submatrix e f)+|beta-1| * fnorm (Z.submatrix e f) := by
      rw [fnorm_smul, fnorm_smul, abs_of_nonneg hb0]
    _ ≤ 2*fnorm (A-C0)+b*2 := by
      apply add_le_add
      · exact mul_le_mul hb (restriction_fnorm _ e f) (norm_nonneg _) (by norm_num)
      · exact mul_le_mul he ((restriction_fnorm Z e f).trans hZ) (norm_nonneg _) hbnon
    _ = _ := by ring
/-- Same supplied controlled root, with its actual squared displacement bound. -/
lemma same_root_join (hm : 0 < m) (Y Z0 : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m → ℝ) (C eps q K B : ℝ)
    (hw : controlledWitness Y C eps q x y) (hK : 0 ≤ K) (heps : 0 ≤ eps)
    (hsq : SameRootFrobeniusCandidate.sqF (expScaled Y x y-Y) ≤ K*eps^2)
    (hbase : fnorm (center Y-center Z0) ≤ B) :
    fnorm (expScaled Y x y-P m-center Z0) ≤ Real.sqrt K*eps+B := by
  have hc := SameRootFrobeniusCandidate.same_root_centering hm Y x y hw
  have hf : fnorm (expScaled Y x y-Y) ≤ Real.sqrt K*eps := by
    rw [← sqrt_frob]
    exact SameRootFrobeniusCandidate.sqrt_squared_bound _ hK heps hsq
  have he : expScaled Y x y-P m-center Z0 = center (expScaled Y x y-Y)+(center Y-center Z0) := by
    change expScaled Y x y-P m-center Y=center (expScaled Y x y-Y) at hc
    rw [← hc]
    abel
  rw [he]
  exact (fnorm_add _ _).trans (add_le_add ((center_fnorm hm _).trans hf) hbase)
/-- Finite normalization estimate with the exact signed-kappa denominator. -/
theorem normalized_displacement (hm : 0 < m) (hn : 0 < (n:ℝ))
    (A C0 Z : Matrix (Fin n) (Fin n) ℝ) (e f : Fin m ↪ Fin n)
    (a t k K : ℝ) (ht : 0 ≤ t) (hdim : (m:ℝ)=(n:ℝ)-t)
    (hk : |k| ≤ K) (hgap : (n:ℝ)/2 ≤ (m:ℝ)-K)
    (hC : C0=Z+constant n a) (hZ : fnorm Z ≤ 2) :
    fnorm (center (((n:ℝ)/((m:ℝ)+k)) • A.submatrix e f)-center (Z.submatrix e f)) ≤
      2*fnorm (A-C0)+4*(t+K)/(n:ℝ) := by
  have hb := NormalizationScalarsCandidate.beta_bounds hn ht hdim hk hgap
  have hh := centered_displacement hm A C0 Z e f a ((n:ℝ)/((m:ℝ)+k))
    (2*(t+K)/(n:ℝ)) hC hb.1.le hb.2.1 hb.2.2 hZ
  convert hh using 1; ring
/-- Actual retained matrix and the same controlled root, no root reselection.
The squared root-error budget is explicit until coefficient-uniform wiring. -/
theorem normalized_same_root_displacement (hm : 0 < m) (hn : 0 < (n:ℝ))
    (A C0 Z : Matrix (Fin n) (Fin n) ℝ) (e f : Fin m ↪ Fin n)
    (a t k K : ℝ) (ht : 0 ≤ t) (hdim : (m:ℝ)=(n:ℝ)-t)
    (hk : |k| ≤ K) (hgap : (n:ℝ)/2 ≤ (m:ℝ)-K)
    (hC : C0=Z+constant n a) (hZ : fnorm Z ≤ 2)
    (x y : Fin m → ℝ) (C eps q Kstar : ℝ)
    (hw : controlledWitness (((n:ℝ)/((m:ℝ)+k)) • A.submatrix e f) C eps q x y)
    (hKs : 0 ≤ Kstar) (heps : 0 ≤ eps)
    (hsq : SameRootFrobeniusCandidate.sqF
      (expScaled (((n:ℝ)/((m:ℝ)+k)) • A.submatrix e f) x y-
        ((n:ℝ)/((m:ℝ)+k)) • A.submatrix e f) ≤ Kstar*eps^2) :
    fnorm (expScaled (((n:ℝ)/((m:ℝ)+k)) • A.submatrix e f) x y-P m-center (Z.submatrix e f)) ≤
      Real.sqrt Kstar*eps+2*fnorm (A-C0)+4*(t+K)/(n:ℝ) := by
  have hbase := normalized_displacement hm hn A C0 Z e f a t k K ht hdim hk hgap hC hZ
  have hh := same_root_join hm _ (Z.submatrix e f) x y C eps q Kstar
    (2*fnorm (A-C0)+4*(t+K)/(n:ℝ)) hw hKs heps hsq hbase
  simpa only [add_assoc] using hh
end FiniteCenteredDisplacementCandidate
