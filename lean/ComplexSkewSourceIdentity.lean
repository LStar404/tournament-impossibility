import Mathlib

/-! Next-stage finite algebra candidate. Not part of the frozen 140-module snapshot.
All source identities below are bilinear (transpose), not Hermitian. -/
noncomputable section
namespace ComplexSkewSourceIdentity
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Commutation with a polynomial passes to its genuine two-sided inverse. -/
lemma commute_resolvent (S R : Matrix ι ι ℂ) (t : ℂ)
    (hleft : R*(1+t • (S*S))=1) (hright : (1+t • (S*S))*R=1) :
    S*R=R*S := by
  let A : Matrix ι ι ℂ := 1+t • (S*S)
  have hAS : A*S=S*A := by
    dsimp [A]
    simp only [add_mul,mul_add,one_mul,mul_one,Matrix.smul_mul,Matrix.mul_smul]
    rw [Matrix.mul_assoc]
  calc
    S*R = (R*A)*(S*R) := by rw [hleft,one_mul]
    _ = R*(A*S)*R := by noncomm_ring
    _ = R*(S*A)*R := by rw [hAS]
    _ = R*S*(A*R) := by noncomm_ring
    _ = R*S := by rw [hright,mul_one]

lemma inverse_sub_one (S R : Matrix ι ι ℂ) (t : ℂ)
    (hleft : R*(1+t • (S*S))=1) :
    R-1=(-t) • (R*(S*S)) := by
  have hh : R+t • (R*(S*S))=1 := by
    simpa only [mul_add,mul_one,Matrix.mul_smul] using hleft
  calc
    R-1 = R-(R+t • (R*(S*S))) := by rw [hh]
    _ = (-t) • (R*(S*S)) := by rw [neg_smul]; abel

/-- The two negative signs, one from skew transpose and one from the resolvent
identity, cancel. No positivity, real parameter, convergence series, or energy
assumption is needed for this finite algebraic identity. -/
theorem bilinear_source (S R : Matrix ι ι ℂ) (t : ℂ) (e : ι → ℂ)
    (hskew : S.transpose= -S)
    (hleft : R*(1+t • (S*S))=1) (hright : (1+t • (S*S))*R=1) :
    e ⬝ᵥ ((R-1).mulVec e) = t*((S.mulVec e) ⬝ᵥ (R.mulVec (S.mulVec e))) := by
  have hcomm := commute_resolvent S R t hleft hright
  have hmat : R*(S*S)=S*R*S := by
    rw [← Matrix.mul_assoc,← hcomm]
  have htranspose := Matrix.dotProduct_transpose_mulVec S e (R.mulVec (S.mulVec e))
  rw [hskew,Matrix.neg_mulVec,dotProduct_neg] at htranspose
  have ht : -(e ⬝ᵥ S.mulVec (R.mulVec (S.mulVec e))) =
      (S.mulVec e) ⬝ᵥ R.mulVec (S.mulVec e) :=
    htranspose.trans (dotProduct_comm _ _)
  have hbil : e ⬝ᵥ ((R*(S*S)).mulVec e) =
      -((S.mulVec e) ⬝ᵥ (R.mulVec (S.mulVec e))) := by
    rw [hmat]
    simp only [← Matrix.mulVec_mulVec]
    linear_combination -ht
  rw [inverse_sub_one S R t hleft,Matrix.smul_mulVec,dotProduct_smul]
  simp only [smul_eq_mul,hbil]
  ring

/-- All-ones specialization: b=S1 is not an independently supplied proxy. -/
theorem ones_source (S R : Matrix ι ι ℂ) (t : ℂ)
    (hskew : S.transpose= -S)
    (hleft : R*(1+t • (S*S))=1) (hright : (1+t • (S*S))*R=1) :
    (fun _ : ι => (1:ℂ)) ⬝ᵥ (R.mulVec (fun _ => 1)) =
      (Fintype.card ι : ℂ)+t*((S.mulVec (fun _ => 1)) ⬝ᵥ
        (R.mulVec (S.mulVec (fun _ => 1)))) := by
  have h := bilinear_source S R t (fun _ => 1) hskew hleft hright
  simp only [Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub] at h
  have he : (fun _ : ι => (1:ℂ)) ⬝ᵥ (fun _ => 1)=(Fintype.card ι : ℂ) := by
    simp [dotProduct]
  rw [he] at h
  linear_combination h

end ComplexSkewSourceIdentity
#print axioms ComplexSkewSourceIdentity.bilinear_source
#print axioms ComplexSkewSourceIdentity.ones_source
