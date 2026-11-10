import ActualTwoSidedCenteringCandidate
set_option autoImplicit false
noncomputable section
namespace RealIndependentRestrictionCandidate
open Matrix Finset RealGramEndpoint RealProjectionAggregationCandidate
open IndependentCenteringEnergyCandidate IndependentDeletionLossCandidate
open scoped Matrix.Norms.L2Operator
variable {n m k : ℕ}
def select (e : Fin m ↪ Fin n) : Matrix (Fin n) (Fin m) ℝ := fun i j=>if i=e j then 1 else 0
lemma select_gram (e : Fin m ↪ Fin n) : (select e)ᵀ*select e=1 := by
  ext i j
  simp [Matrix.mul_apply,Matrix.transpose_apply,select,Matrix.one_apply,e.injective.eq_iff,eq_comm]
lemma select_norm (e : Fin m ↪ Fin n) : ‖select e‖≤1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (select e)
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial,select_gram] at hh
  have hi : ‖(1 : Matrix (Fin m) (Fin m) ℝ)‖≤1 := by
    rw [←Matrix.l2_opNorm_toEuclideanCLM,map_one]
    exact ContinuousLinearMap.norm_id_le
  have hn := norm_nonneg (select e)
  nlinarith
lemma row_projection (e : Fin m ↪ Fin n) :
    (select e*(select e)ᵀ)ᵀ=select e*(select e)ᵀ ∧
    (select e*(select e)ᵀ)*(select e*(select e)ᵀ)=select e*(select e)ᵀ := by
  constructor
  · simp only [Matrix.transpose_mul,Matrix.transpose_transpose]
  · calc
      _ = select e*((select e)ᵀ*select e)*(select e)ᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [select_gram,Matrix.mul_one]
lemma row_gram (Z : Matrix (Fin n) (Fin k) ℝ) (e : Fin m ↪ Fin n) :
    ((select e)ᵀ*Z)ᵀ*((select e)ᵀ*Z)=Zᵀ*(select e*(select e)ᵀ)*Z := by
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
lemma restriction_operator (Z : Matrix (Fin n) (Fin k) ℝ) (e : Fin m ↪ Fin n) :
    ‖(select e)ᵀ*Z‖≤‖Z‖ := by
  have he : ‖(select e)ᵀ‖≤1 := by simpa only [←Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.l2_opNorm_conjTranspose] using select_norm e
  exact (Matrix.l2_opNorm_mul (select e)ᵀ Z).trans ((mul_le_mul_of_nonneg_right he (norm_nonneg Z)).trans_eq (one_mul _))
lemma row_g_loss (Z : Matrix (Fin n) (Fin k) ℝ) (e : Fin m ↪ Fin n)
    (q : ℝ) (hq : 0≤q) (hq1 : q<1) (hZ : ‖Z‖≤q) :
    ‖g ((select e)ᵀ*Z)-g Z‖≤(frob Z-frob ((select e)ᵀ*Z))/(2*(1-q^2)) := by
  have hp := row_projection e
  have hh := left_g_loss Z (select e*(select e)ᵀ) hp.1 hp.2 q hq hq1 hZ
  have hg : g ((select e)ᵀ*Z)=g ((select e*(select e)ᵀ)*Z) := by
    simp only [g,row_gram,projected_gram Z _ hp.1 hp.2]
  have hf : frob ((select e)ᵀ*Z)=frob ((select e*(select e)ᵀ)*Z) := by
    rw [←trace_gram,←trace_gram,row_gram,projected_gram Z _ hp.1 hp.2]
  rw [frob_loss Z _ hp.1 hp.2,←hg,←hf] at hh
  exact hh
lemma column_g_loss (Z : Matrix (Fin k) (Fin n) ℝ) (f : Fin m ↪ Fin n)
    (q : ℝ) (hq : 0≤q) (hq1 : q<1) (hZ : ‖Z‖≤q) :
    ‖g (Z*select f)-g Z‖≤(frob Z-frob (Z*select f))/(2*(1-q^2)) := by
  have hh := row_g_loss Zᵀ f q hq hq1 (by simpa only [←Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.l2_opNorm_conjTranspose] using hZ)
  have he : (select f)ᵀ*Zᵀ=(Z*select f)ᵀ := (Matrix.transpose_mul _ _).symm
  simpa only [he,g_transpose,frob_transpose] using hh
lemma selection_submatrix (Z : Matrix (Fin n) (Fin n) ℝ) (e f : Fin m ↪ Fin n) :
    (select e)ᵀ*Z*select f=Z.submatrix e f := by
  ext i j
  simp [Matrix.mul_apply,Matrix.transpose_apply,select,Matrix.submatrix]
lemma independent_g_loss (Z : Matrix (Fin n) (Fin n) ℝ) (e f : Fin m ↪ Fin n)
    (q : ℝ) (hq : 0≤q) (hq1 : q<1) (hZ : ‖Z‖≤q) :
    ‖g (Z.submatrix e f)-g Z‖≤(frob Z-frob (Z.submatrix e f))/(2*(1-q^2)) := by
  have hr := row_g_loss Z e q hq hq1 hZ
  have hc := column_g_loss ((select e)ᵀ*Z) f q hq hq1 ((restriction_operator Z e).trans hZ)
  rw [selection_submatrix] at hc
  calc
    _ ≤ ‖g (Z.submatrix e f)-g ((select e)ᵀ*Z)‖+‖g ((select e)ᵀ*Z)-g Z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hc hr
    _ = _ := by ring
lemma complexification_frob {r c : ℕ} (Z : Matrix (Fin r) (Fin c) ℝ) :
    RectangularGramLossCandidate.frobeniusSq (fun i j=>(Z i j:ℂ))=frob Z := by
  simp only [RectangularGramLossCandidate.frobeniusSq,frob,Complex.norm_real,Real.norm_eq_abs,sq_abs]
lemma actual_frob_deletion (T : TournamentHamiltonian.Tournament n) (e f : Fin m ↪ Fin n)
    (t : ℕ) (hm : n=m+t) :
    frob (realZ T)-frob ((realZ T).submatrix e f)=(t:ℝ)*((n:ℝ)+(m:ℝ))/((n:ℝ)-1)^2 := by
  have hh := actual_independent_deletion_loss T e f t hm
  change RectangularGramLossCandidate.frobeniusSq (fun i j=>(realZ T i j:ℂ))-
    RectangularGramLossCandidate.frobeniusSq (fun i j=>((realZ T).submatrix e f i j:ℂ))=_ at hh
  simpa only [complexification_frob] using hh
theorem actual_deletion_g_bound (T : TournamentHamiltonian.Tournament n) (e f : Fin m ↪ Fin n)
    (t : ℕ) (hm : n=m+t) (q : ℝ) (hq : 0≤q) (hq1 : q<1) (hZ : ‖realZ T‖≤q) :
    ‖g ((realZ T).submatrix e f)-g (realZ T)‖ ≤
      ((t:ℝ)*((n:ℝ)+(m:ℝ))/((n:ℝ)-1)^2)/(2*(1-q^2)) := by
  simpa only [actual_frob_deletion T e f t hm] using independent_g_loss (realZ T) e f q hq hq1 hZ
end RealIndependentRestrictionCandidate

#print axioms RealIndependentRestrictionCandidate.select
#check RealIndependentRestrictionCandidate.select

#print axioms RealIndependentRestrictionCandidate.select_gram
#check RealIndependentRestrictionCandidate.select_gram

#print axioms RealIndependentRestrictionCandidate.select_norm
#check RealIndependentRestrictionCandidate.select_norm

#print axioms RealIndependentRestrictionCandidate.row_projection
#check RealIndependentRestrictionCandidate.row_projection

#print axioms RealIndependentRestrictionCandidate.row_gram
#check RealIndependentRestrictionCandidate.row_gram

#print axioms RealIndependentRestrictionCandidate.restriction_operator
#check RealIndependentRestrictionCandidate.restriction_operator

#print axioms RealIndependentRestrictionCandidate.row_g_loss
#check RealIndependentRestrictionCandidate.row_g_loss

#print axioms RealIndependentRestrictionCandidate.column_g_loss
#check RealIndependentRestrictionCandidate.column_g_loss

#print axioms RealIndependentRestrictionCandidate.selection_submatrix
#check RealIndependentRestrictionCandidate.selection_submatrix

#print axioms RealIndependentRestrictionCandidate.independent_g_loss
#check RealIndependentRestrictionCandidate.independent_g_loss

#print axioms RealIndependentRestrictionCandidate.complexification_frob
#check RealIndependentRestrictionCandidate.complexification_frob

#print axioms RealIndependentRestrictionCandidate.actual_frob_deletion
#check RealIndependentRestrictionCandidate.actual_frob_deletion

#print axioms RealIndependentRestrictionCandidate.actual_deletion_g_bound
#check RealIndependentRestrictionCandidate.actual_deletion_g_bound
