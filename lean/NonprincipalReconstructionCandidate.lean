import DiagonalScalingPermanent
import TournamentPrescalingMass
set_option autoImplicit false
noncomputable section
namespace NonprincipalReconstructionCandidate
open Finset MatrixScalingMassPotential
variable {n m : ℕ}

def gamma (a : Fin n → ℝ) : ℝ := ∏ i, (1-(a i)^2)
def pre (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (1+a i)⁻¹ * (2*A i j/((n:ℝ)-1)) * (1-a j)⁻¹
def nu (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, pre A a i j)-(n:ℝ)
def normalizedPre (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((n:ℝ)/((n:ℝ)+nu A a)) • pre A a
def deletedX (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (r c : Fin m → Fin n) : Matrix (Fin m) (Fin m) ℝ :=
  ((n:ℝ)/(m:ℝ)) • (normalizedPre A a).submatrix r c

def scale (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (m : ℕ) : ℝ :=
  (m:ℝ)*((n:ℝ)-1)*((n:ℝ)+nu A a)/(2*(n:ℝ)^2)

lemma matrix_reconstruction (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (r c : Fin m → Fin n) (hn : 1 < n) (hm : 0 < m)
    (ha : ∀ i, |a i|<1) (hnu : (n:ℝ)+nu A a≠0) :
    A.submatrix r c = fun i j =>
      scale A a m*(1+a (r i))*(deletedX A a r c i j)*(1-a (c j)) := by
  ext i j
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hn1 : (n:ℝ)-1≠0 := by
    have hh : (1:ℝ)<n := by exact_mod_cast hn
    linarith
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hp : 1+a (r i)≠0 := by have hh := abs_lt.mp (ha (r i)); linarith
  have hq : 1-a (c j)≠0 := by have hh := abs_lt.mp (ha (c j)); linarith
  simp only [scale,deletedX,normalizedPre,pre,Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp [hn0,hn1,hm0,hp,hq,hnu]

/-- Pure finite permanent factor extraction, no positivity or scaling existence. -/
lemma permanent_factors (X : Matrix (Fin m) (Fin m) ℝ) (k : ℝ) (l r : Fin m → ℝ) :
    Matrix.permanent (fun i j => k*l i*X i j*r j) =
      k^m*(∏ i, l i)*(∏ j, r j)*X.permanent := by
  unfold Matrix.permanent
  have hterm (σ : Equiv.Perm (Fin m)) :
      (∏ i, k*l (σ i)*X (σ i) i*r i) = k^m*(∏ i, l i)*(∏ j, r j)*(∏ i,X (σ i) i) := by
    simp only [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,Equiv.prod_comp]
    ring
  simp_rw [hterm]
  rw [← mul_sum]

/-- Complement recovery is inverse deleted weight, not omission of full product. -/
lemma complement_product (f : Fin n → ℝ) (I : Finset (Fin n)) (hf : ∀ i,f i≠0) :
    (∏ i ∈ Iᶜ, f i) = (∏ i,f i)*(∏ i ∈ I,(f i)⁻¹) := by
  have hi : (∏ i ∈ I,f i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)
  have hh := Finset.prod_mul_prod_compl I f
  rw [Finset.prod_inv_distrib]
  field_simp [hi]
  nlinarith [hh]

lemma retained_gamma (a : Fin n → ℝ) (I J : Finset (Fin n)) (ha : ∀ i,|a i|<1) :
    (∏ i ∈ Iᶜ, (1+a i))*(∏ j ∈ Jᶜ, (1-a j)) =
      gamma a*(∏ i ∈ I,(1+a i)⁻¹)*(∏ j ∈ J,(1-a j)⁻¹) := by
  have hp (i) : 1+a i≠0 := by have hh := abs_lt.mp (ha i); linarith
  have hq (i) : 1-a i≠0 := by have hh := abs_lt.mp (ha i); linarith
  rw [complement_product _ I hp,complement_product _ J hq]
  have hg : gamma a=(∏ i, (1+a i))*(∏ i, (1-a i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [hg]
  ring

/-- Actual indexed independent deletion. r and c enumerate different complements. -/
theorem exact_reconstruction (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (hn : 1 < n) (hm : 0 < m) (ha : ∀ i,|a i|<1)
    (hnu : (n:ℝ)+nu A a≠0) (x y : Fin m → ℝ) :
    let rr := fun i => (r i).val
    let cc := fun j => (c j).val
    (A.submatrix rr cc).permanent =
      gamma a*(∏ i ∈ I,(1+a i)⁻¹)*(∏ j ∈ J,(1-a j)⁻¹)*
      (scale A a m)^m*Real.exp (-theta x y)*
      (expScaled (deletedX A a rr cc) x y).permanent := by
  dsimp only
  rw [matrix_reconstruction A a _ _ hn hm ha hnu,permanent_factors]
  have hr : (∏ i : Fin m, (1+a (r i).val)) = ∏ i ∈ Iᶜ, (1+a i) := by
    rw [Equiv.prod_comp r (fun i : {i // i ∈ Iᶜ} => 1+a i.val)]
    exact (Finset.prod_subtype Iᶜ (fun _ => Iff.rfl) (fun i => 1+a i)).symm
  have hc : (∏ j : Fin m, (1-a (c j).val)) = ∏ j ∈ Jᶜ, (1-a j) := by
    rw [Equiv.prod_comp c (fun j : {j // j ∈ Jᶜ} => 1-a j.val)]
    exact (Finset.prod_subtype Jᶜ (fun _ => Iff.rfl) (fun j => 1-a j)).symm
  rw [hr,hc,DiagonalScalingPermanent.permanent_recovery (deletedX A a _ _) x y]
  have hg := retained_gamma a I J ha
  rw [mul_assoc ((scale A a m)^m), hg]
  ring

/-- Correct sign for X: only theta >= -kappa, regardless of reconstruction. -/
theorem actual_potential_bound (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (r c : Fin m → Fin n) (x y : Fin m → ℝ)
    (hX : ∀ i j,0≤deletedX A a r c i j)
    (hr : ∀ i,∑ j,expScaled (deletedX A a r c) x y i j=1)
    (hc : ∀ j,∑ i,expScaled (deletedX A a r c) x y i j=1) :
    -kappa (deletedX A a r c)≤theta x y :=
  theta_ge_neg_kappa _ x y hX hr hc
/-- Transfer a root of Y=cX to X, distributing log c equally across the gauges. -/
lemma positive_scalar_root_transfer (X : Matrix (Fin m) (Fin m) ℝ)
    (c : ℝ) (hc : 0<c) (x y : Fin m → ℝ) :
    expScaled X (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2) =
      expScaled (c • X) x y := by
  ext i j
  have heq : (x i+Real.log c/2)+(y j+Real.log c/2) = (x i+y j)+Real.log c := by ring
  simp only [expScaled,Matrix.smul_apply,smul_eq_mul,heq,Real.exp_add,Real.exp_log hc]
  ring

lemma positive_scalar_potential_transfer (c : ℝ) (x y : Fin m → ℝ) :
    theta (fun i => x i+Real.log c/2) (fun j => y j+Real.log c/2) =
      theta x y+(m:ℝ)*Real.log c := by
  simp only [theta,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- The transfer preserves the zero sum of the row-column gauge difference. -/
lemma positive_scalar_gauge_transfer (c : ℝ) (x y : Fin m → ℝ) :
    (∑ i,(x i+Real.log c/2))-(∑ j,(y j+Real.log c/2)) = (∑ i,x i)-(∑ j,y j) := by
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring
end NonprincipalReconstructionCandidate

#print axioms NonprincipalReconstructionCandidate.gamma
#check NonprincipalReconstructionCandidate.gamma
#print axioms NonprincipalReconstructionCandidate.pre
#check NonprincipalReconstructionCandidate.pre
#print axioms NonprincipalReconstructionCandidate.nu
#check NonprincipalReconstructionCandidate.nu
#print axioms NonprincipalReconstructionCandidate.normalizedPre
#check NonprincipalReconstructionCandidate.normalizedPre
#print axioms NonprincipalReconstructionCandidate.deletedX
#check NonprincipalReconstructionCandidate.deletedX
#print axioms NonprincipalReconstructionCandidate.scale
#check NonprincipalReconstructionCandidate.scale
#print axioms NonprincipalReconstructionCandidate.matrix_reconstruction
#check NonprincipalReconstructionCandidate.matrix_reconstruction
#print axioms NonprincipalReconstructionCandidate.permanent_factors
#check NonprincipalReconstructionCandidate.permanent_factors
#print axioms NonprincipalReconstructionCandidate.complement_product
#check NonprincipalReconstructionCandidate.complement_product
#print axioms NonprincipalReconstructionCandidate.retained_gamma
#check NonprincipalReconstructionCandidate.retained_gamma
#print axioms NonprincipalReconstructionCandidate.exact_reconstruction
#check NonprincipalReconstructionCandidate.exact_reconstruction
#print axioms NonprincipalReconstructionCandidate.actual_potential_bound
#check NonprincipalReconstructionCandidate.actual_potential_bound
#print axioms NonprincipalReconstructionCandidate.positive_scalar_root_transfer
#check NonprincipalReconstructionCandidate.positive_scalar_root_transfer
#print axioms NonprincipalReconstructionCandidate.positive_scalar_potential_transfer
#check NonprincipalReconstructionCandidate.positive_scalar_potential_transfer
#print axioms NonprincipalReconstructionCandidate.positive_scalar_gauge_transfer
#check NonprincipalReconstructionCandidate.positive_scalar_gauge_transfer
