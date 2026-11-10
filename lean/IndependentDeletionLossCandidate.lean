import Mathlib.LinearAlgebra.Matrix.SchurComplement
import RectangularGramLossCandidate
import IndependentCenteredRestrictionCandidate
import ActualTournamentPrescalingBounds
set_option autoImplicit false
noncomputable section
namespace IndependentDeletionLossCandidate
open Matrix Finset TournamentHamiltonian
open RectangularGramLossCandidate IndependentCenteredRestrictionCandidate
variable {n m k : ℕ}
def selectionProjection (e : Fin m ↪ Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  selection e * (selection e)ᴴ
lemma selectionProjection_adjoint (e : Fin m ↪ Fin n) :
    (selectionProjection e)ᴴ=selectionProjection e := by
  simp [selectionProjection, Matrix.conjTranspose_mul]
lemma selectionProjection_idempotent (e : Fin m ↪ Fin n) :
    selectionProjection e * selectionProjection e=selectionProjection e := by
  unfold selectionProjection
  calc
    _ = selection e * ((selection e)ᴴ * selection e) * (selection e)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [selection_gram,Matrix.mul_one]
lemma retained_row_gram (Z : Matrix (Fin n) (Fin k) ℂ) (e : Fin m ↪ Fin n) :
    ((selection e)ᴴ*Z)ᴴ*((selection e)ᴴ*Z) =
      (selectionProjection e*Z)ᴴ*(selectionProjection e*Z) := by
  rw [projected_gram Z _ (selectionProjection_adjoint e) (selectionProjection_idempotent e)]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,selectionProjection,Matrix.mul_assoc]
lemma row_loss_trace (Z : Matrix (Fin n) (Fin k) ℂ) (e : Fin m ↪ Fin n) :
    (gramLoss Z (selectionProjection e)).trace =
      ((frobeniusSq Z-frobeniusSq ((selection e)ᴴ*Z):ℝ):ℂ) := by
  rw [← gram_difference Z _ (selectionProjection_adjoint e) (selectionProjection_idempotent e),
    ← retained_row_gram, Matrix.trace_sub, trace_gram,trace_gram]
  exact (Complex.ofReal_sub _ _).symm
lemma row_restriction (Z : Matrix (Fin n) (Fin k) ℂ) (e : Fin m ↪ Fin n) (i : Fin m) (j : Fin k) :
    ((selection e)ᴴ*Z) i j=Z (e i) j := by
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,selection]
lemma constant_frobenius {r c : ℕ} (Z : Matrix (Fin r) (Fin c) ℂ) (d : ℝ)
    (hZ : ∀ i j,‖Z i j‖^2=d) : frobeniusSq Z=(r:ℝ)*(c:ℝ)*d := by
  simp only [frobeniusSq,hZ,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring
lemma constant_independent_deletion (Z : Matrix (Fin n) (Fin n) ℂ)
    (e f : Fin m ↪ Fin n) (t : ℕ) (hm : n=m+t) (d : ℝ)
    (hZ : ∀ i j,‖Z i j‖^2=d) :
    frobeniusSq Z-frobeniusSq (Z.submatrix e f)=(t:ℝ)*((n:ℝ)+(m:ℝ))*d := by
  rw [constant_frobenius Z d hZ, constant_frobenius (Z.submatrix e f) d (fun i j=>hZ (e i) (f j)),hm]
  push_cast
  ring

def actualZ (T : Tournament n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (((signMatrix T i j-(if i=j then 1 else 0))/((n:ℝ)-1):ℝ):ℂ)
lemma actualZ_entry_square (T : Tournament n) (i j : Fin n) :
    ‖actualZ T i j‖^2=1/((n:ℝ)-1)^2 := by
  simp only [actualZ,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow]
  have hh := signMatrix_sq T i j
  by_cases hij : i=j
  · subst j
    simp [signMatrix]
  · simp only [if_neg hij,sub_zero] at *
    rw [hh]
lemma actual_independent_deletion_loss (T : Tournament n)
    (e f : Fin m ↪ Fin n) (t : ℕ) (hm : n=m+t) :
    frobeniusSq (actualZ T)-frobeniusSq ((actualZ T).submatrix e f)=
      (t:ℝ)*((n:ℝ)+(m:ℝ))/((n:ℝ)-1)^2 := by
  rw [constant_independent_deletion (actualZ T) e f t hm _ (actualZ_entry_square T)]
  ring
lemma rectangular_sylvester (W : Matrix (Fin n) (Fin m) ℂ) :
    (1-Wᴴ*W).det=(1-W*Wᴴ).det := Matrix.det_one_sub_mul_comm Wᴴ W
lemma rectangular_real_logdet (W : Matrix (Fin n) (Fin m) ℝ) :
    -(1/2:ℝ)*Real.log ((1-W.transpose*W).det)=
      -(1/2:ℝ)*Real.log ((1-W*W.transpose).det) := by
  rw [Matrix.det_one_sub_mul_comm W.transpose W]
end IndependentDeletionLossCandidate

#print axioms IndependentDeletionLossCandidate.selectionProjection
#check IndependentDeletionLossCandidate.selectionProjection

#print axioms IndependentDeletionLossCandidate.selectionProjection_adjoint
#check IndependentDeletionLossCandidate.selectionProjection_adjoint

#print axioms IndependentDeletionLossCandidate.selectionProjection_idempotent
#check IndependentDeletionLossCandidate.selectionProjection_idempotent

#print axioms IndependentDeletionLossCandidate.retained_row_gram
#check IndependentDeletionLossCandidate.retained_row_gram

#print axioms IndependentDeletionLossCandidate.row_loss_trace
#check IndependentDeletionLossCandidate.row_loss_trace

#print axioms IndependentDeletionLossCandidate.row_restriction
#check IndependentDeletionLossCandidate.row_restriction

#print axioms IndependentDeletionLossCandidate.constant_frobenius
#check IndependentDeletionLossCandidate.constant_frobenius

#print axioms IndependentDeletionLossCandidate.constant_independent_deletion
#check IndependentDeletionLossCandidate.constant_independent_deletion

#print axioms IndependentDeletionLossCandidate.actualZ
#check IndependentDeletionLossCandidate.actualZ

#print axioms IndependentDeletionLossCandidate.actualZ_entry_square
#check IndependentDeletionLossCandidate.actualZ_entry_square

#print axioms IndependentDeletionLossCandidate.actual_independent_deletion_loss
#check IndependentDeletionLossCandidate.actual_independent_deletion_loss

#print axioms IndependentDeletionLossCandidate.rectangular_sylvester
#check IndependentDeletionLossCandidate.rectangular_sylvester
#print axioms IndependentDeletionLossCandidate.rectangular_real_logdet
#check IndependentDeletionLossCandidate.rectangular_real_logdet
