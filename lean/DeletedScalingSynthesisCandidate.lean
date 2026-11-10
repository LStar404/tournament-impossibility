import ActualNormalizedCenteredGapCandidate
import NormalizedCenteredRestrictionCandidate
import RawScalingSynthesis

/-! Verified in the 557-module direct-Lean compilation and declaration audit. Same-matrix independent deletion/scaling wiring.
All target marginal and real centered-operator bounds are derived. -/
set_option autoImplicit false
noncomputable section
namespace DeletedScalingSynthesisCandidate
open Matrix Finset
open scoped Matrix.Norms.L2Operator
open IndependentCenteredRestrictionCandidate NormalizedCenteredRestrictionCandidate
open DeletionRenormalizationCandidate ActualHessianFinite ActualHessianComplex
open MatrixScalingMassPotential ActualNormalizedCenteredGapCandidate
variable {n m : ℕ}

def deleted (A : Matrix (Fin n) (Fin n) ℝ) (e f : Fin m ↪ Fin n) (k : ℝ) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => (n:ℝ)/((m:ℝ)+k)*A (e i) (f j)

def density (m : ℕ) (C K : ℝ) := C*(m:ℝ)/((m:ℝ)-K)
def residualBudget (n m : ℕ) (t C δ K : ℝ) :=
  ((n:ℝ)*δ+(C+1)*t+K)/((m:ℝ)-K)
def gapBudget (n m : ℕ) (q K : ℝ) := (n:ℝ)*q/((m:ℝ)-K)

lemma removed_mass (A : Matrix (Fin n) (Fin n) ℝ) (J : Finset (Fin n))
    {C : ℝ} (hA : ∀ i j, 0 ≤ A i j) (hd : ∀ i j, A i j ≤ C/(n:ℝ)) (i : Fin n) :
    0 ≤ ∑ j ∈ J,A i j ∧ (∑ j ∈ J,A i j) ≤ C*(J.card:ℝ)/(n:ℝ) := by
  constructor
  · exact sum_nonneg (fun j _ => hA i j)
  · calc
      _ ≤ ∑ _j ∈ J,C/(n:ℝ) := sum_le_sum (fun j _ => hd i j)
      _ = _ := by simp; ring

lemma deleted_rows (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (e f : Fin m ↪ Fin n) (I J : Finset (Fin n))
    (hf : univ.image f=Jᶜ) (hcard : J.card=I.card)
    (hm : (m:ℝ)=(n:ℝ)-(I.card:ℝ))
    {C δ k K : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hK : |k| ≤ K) (hsmall : K < (m:ℝ))
    (hA : ∀ i j,0 ≤ A i j) (hd : ∀ i j,A i j ≤ C/(n:ℝ))
    (hr : ∀ i, |IndependentDeletionMass.rowResidual A i| ≤ δ) (i : Fin m) :
    |(∑ j,deleted A e f k i j)-1| ≤ residualBudget n m I.card C δ K := by
  have hmass := removed_mass A J hA hd (e i)
  rw [hcard] at hmass
  have hh := marginal_bound (show (0:ℝ)<n by exact_mod_cast hn)
    (show (0:ℝ)≤I.card by positivity) hC hδ hm hK hsmall (hr (e i)) hmass.1 hmass.2
  simpa [deleted, ← mul_sum, retained_row_mass A f J hf (e i), residualBudget] using hh

lemma deleted_cols (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (e f : Fin m ↪ Fin n) (I _J : Finset (Fin n))
    (he : univ.image e=Iᶜ) (hm : (m:ℝ)=(n:ℝ)-(I.card:ℝ))
    {C δ k K : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hK : |k| ≤ K) (hsmall : K < (m:ℝ))
    (hA : ∀ i j,0 ≤ A i j) (hd : ∀ i j,A i j ≤ C/(n:ℝ))
    (hc : ∀ j, |IndependentDeletionMass.colResidual A j| ≤ δ) (j : Fin m) :
    |(∑ i,deleted A e f k i j)-1| ≤ residualBudget n m I.card C δ K := by
  have hmass := removed_mass A.transpose I (fun i j => hA j i) (fun i j => hd j i) (f j)
  have hh := marginal_bound (show (0:ℝ)<n by exact_mod_cast hn)
    (show (0:ℝ)≤I.card by positivity) hC hδ hm hK hsmall (hc (f j)) hmass.1 hmass.2
  simpa [deleted, ← mul_sum, retained_col_mass A e I he (f j), residualBudget,
    Matrix.transpose_apply] using hh

lemma deleted_real_gap (hm : 0 < m) (A : Matrix (Fin n) (Fin n) ℝ)
    (e f : Fin m ↪ Fin n) {q k K : ℝ} (hq : 0 ≤ q)
    (hK : |k| ≤ K) (hsmall : K < (m:ℝ))
    (hA : ‖proj n*castMatrix A*proj n‖ ≤ q) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=Fin m) ((1-P m)*deleted A e f k*(1-P m))‖ ≤
      gapBudget n m q K := by
  have hq' : 0 ≤ gapBudget n m q K := by unfold gapBudget; positivity
  apply RawScalingSynthesis.real_gap_of_complex _ hq'
  have hcast : realComplex (deleted A e f k) =
      (((n:ℝ)/((m:ℝ)+k):ℂ) • (castMatrix A).submatrix e f) := by
    ext i j
    simp [realComplex, deleted, castMatrix, ComplexifiedSkewBound.complexify]
  rw [realComplex_mul, realComplex_mul, ScalingCenteredGap.cast_Pi, hcast]
  change ‖Matrix.toEuclideanCLM (𝕜:=ℂ)
    (proj m*(((n:ℝ)/((m:ℝ)+k):ℂ) • (castMatrix A).submatrix e f)*proj m)‖ ≤ _
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  exact normalized_centered_bound hm (castMatrix A) e f hq hK hsmall hA

/-- Preserve every same-root estimate needed downstream. -/
def controlled (M : Matrix (Fin m) (Fin m) ℝ) (C ε q : ℝ) : Prop :=
  let a := RawScalingSynthesis.radius C q ε
  ∃ x y : Fin m → ℝ,
    ‖ActualRootEnergy.vector x y‖ ≤ a ∧
    (∑ i,x i) = ∑ j,y j ∧
    ActualRootEnergy.root M x y ∧
    FiniteSymmetricQuadratic.l2 (ActualRootEnergy.vector x y) ≤
      Real.exp (2*a)/(1-q-4*ε)*FiniteSymmetricQuadratic.l2 (ActualRootEnergy.residual M) ∧
    (∀ i j,0 ≤ expScaled M x y i j ∧ expScaled M x y i j ≤ Real.exp (2*a)*(C/(m:ℝ))) ∧
    (∑ i,∑ j,(expScaled M x y i j-M i j)^2) ≤
      (2*C*(1+ε)*Real.exp (4*a)/(m:ℝ))*(Real.exp (2*a)/(1-q-4*ε))^2*
        FiniteSymmetricQuadratic.energy (ActualRootEnergy.residual M) ∧
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (realComplex (expScaled M x y-P m))‖ ≤
      q+(1+ε)*(Real.exp (2*a)-1) ∧
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (realComplex (expScaled M x y-P m))‖ ≤ (1+q)/2 ∧
    (1+q)/2 < 1

/-- Root and final gap are for the very same explicit deleted matrix. -/
theorem exists_deleted_scaling (hn : 0 < n) (hm0 : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℝ) (e f : Fin m ↪ Fin n)
    (I J : Finset (Fin n)) (he : univ.image e=Iᶜ) (hf : univ.image f=Jᶜ)
    (hcard : J.card=I.card) (hm : (m:ℝ)=(n:ℝ)-(I.card:ℝ))
    {C δ q k K : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hq : 0 ≤ q)
    (hK : |k| ≤ K) (hsmall : K < (m:ℝ))
    (hA : ∀ i j,0 ≤ A i j) (hd : ∀ i j,A i j ≤ C/(n:ℝ))
    (hr : ∀ i, |IndependentDeletionMass.rowResidual A i| ≤ δ)
    (hc : ∀ j, |IndependentDeletionMass.colResidual A j| ≤ δ)
    (hgap : ‖proj n*castMatrix A*proj n‖ ≤ q)
    (hgap' : gapBudget n m q K < 1)
    (hthreshold : residualBudget n m I.card C δ K ≤
      RawScalingSynthesis.epsilonThreshold (density m C K) (gapBudget n m q K)) :
    controlled (deleted A e f k) (density m C K)
      (residualBudget n m I.card C δ K) (gapBudget n m q K) := by
  have hden := denominator_pos hK hsmall
  have hK0 : 0 ≤ K := (abs_nonneg k).trans hK
  have hC' : 0 ≤ density m C K := by unfold density; positivity
  have hε : 0 ≤ residualBudget n m I.card C δ K := by unfold residualBudget; positivity
  have hq' : 0 ≤ gapBudget n m q K := by unfold gapBudget; positivity
  have hpos : ∀ i j,0 ≤ deleted A e f k i j := by
    intro i j
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg n) hden.le) (hA _ _)
  have hentry : ∀ i j,deleted A e f k i j ≤ density m C K/(m:ℝ) := by
    intro i j
    have hh := density_bound (show (0:ℝ)<n by exact_mod_cast hn) hK hsmall (hd (e i) (f j)) hC
    have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm0
    convert hh using 1
    · rfl
    · unfold density
      field_simp
  have hrs : ∀ i, |r (deleted A e f k) i| ≤ residualBudget n m I.card C δ K := by
    intro i
    exact deleted_rows hn A e f I J hf hcard hm hC hδ hK hsmall hA hd hr i
  have hcs : ∀ j, |c (deleted A e f k) j| ≤ residualBudget n m I.card C δ K := by
    intro j
    exact deleted_cols hn A e f I J he hm hC hδ hK hsmall hA hd hc j
  exact RawScalingSynthesis.exists_controlled_scaling hm0 (deleted A e f k) hC' hε hthreshold
      hpos hentry hrs hcs hq' hgap' (deleted_real_gap hm0 A e f hq hK hsmall hgap)

open TournamentHamiltonian ActualTournamentPrescalingBounds ActualPrescalingNormalization

def actualK (T : Tournament n) (a0 : ℝ) (I : Finset (Fin n)) : ℝ :=
  4*(I.card:ℝ)*normalizedMarginalBound T a0+
    2*(16*(scaleCap a0)^2+1)*(I.card:ℝ)^2/(n:ℝ)

def actualDeleted (T : Tournament n) (e f : Fin m ↪ Fin n) (I J : Finset (Fin n)) :=
  deleted (normalizedMatrix T) e f (IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J)

/-- Actual object instantiation. Smallness is explicit numerical budget, not
an assumed target inverse, scaling root, or centered spectral estimate. -/
theorem actual_deleted_scaling (T : Tournament n) (hn : 24 ≤ n) (hm0 : 0 < m)
    (e f : Fin m ↪ Fin n) (I J : Finset (Fin n))
    (he : univ.image e=Iᶜ) (hf : univ.image f=Jᶜ)
    (hcard : J.card=I.card) (hhalf : 2*I.card ≤ n)
    (hm : (m:ℝ)=(n:ℝ)-(I.card:ℝ))
    {a0 : ℝ} (h0 : 0 ≤ a0) (h1 : a0<1)
    (ha : ∀ i,|normalizedScore T i| ≤ a0)
    (herr : Real.sqrt (errorBudget T a0) ≤ 1/46)
    (hsmall : actualK T a0 I < (m:ℝ))
    (hgap : gapBudget n m (39/46) (actualK T a0 I) < 1)
    (hthreshold : residualBudget n m I.card (16*(scaleCap a0)^2)
        (normalizedMarginalBound T a0) (actualK T a0 I) ≤
      RawScalingSynthesis.epsilonThreshold (density m (16*(scaleCap a0)^2) (actualK T a0 I))
        (gapBudget n m (39/46) (actualK T a0 I))) :
    controlled (actualDeleted T e f I J) (density m (16*(scaleCap a0)^2) (actualK T a0 I))
      (residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I))
      (gapBudget n m (39/46) (actualK T a0 I)) := by
  have hn2 : 2 ≤ n := by omega
  have hκ := actual_independent_deletion_bound T hn2 h0 h1 ha I J hcard hhalf
  have hmarg := normalized_marginals T hn2 h0 h1 ha
  apply exists_deleted_scaling (by omega) hm0 (normalizedMatrix T) e f I J he hf hcard hm
    (by positivity) (normalizedMarginalBound_nonneg T a0) (by norm_num)
    hκ hsmall (normalized_nonneg T hn2 h0 h1 ha)
    (fun i j => (le_abs_self _).trans (normalized_entry_bound T hn2 h0 h1 ha i j))
    hmarg.1 hmarg.2 (actual_fixed_gap T hn h0 h1 ha herr) hgap hthreshold

end DeletedScalingSynthesisCandidate
