import Mathlib

/-! Independent next-stage draft: not included in the frozen 140-module snapshot. -/
noncomputable section
namespace BlockGaussianSourceElimination
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def blockSystem (S : Matrix ι ι ℂ) (α v : ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  fromBlocks 1 (α • (S+v • 1)) (α • (-S+v • 1)) 1

lemma sum_difference_equations (S : Matrix ι ι ℂ) (α v : ℂ) (x y e : ι → ℂ)
    (hx : x+α • (S.mulVec y+v • y)=e)
    (hy : y+α • (-S.mulVec x+v • x)=e) :
    (1+v*α) • (x+y)-α • (S.mulVec (x-y))=2 • e ∧
    (1-v*α) • (x-y)+α • (S.mulVec (x+y))=0 := by
  constructor
  · calc
      _ = (x+α • (S.mulVec y+v • y))+(y+α • (-S.mulVec x+v • x)) := by
        simp only [Matrix.mulVec_sub]
        module
      _ = e+e := by rw [hx,hy]
      _ = 2 • e := by module
  · calc
      _ = (x+α • (S.mulVec y+v • y))-(y+α • (-S.mulVec x+v • x)) := by
        simp only [Matrix.mulVec_add]
        module
      _ = 0 := by rw [hx,hy,sub_self]

/-- Elimination is purely finite algebra. beta is made explicit, and t must
satisfy beta*t=alpha^2, as the chosen Gaussian branch later guarantees. -/
theorem eliminate (S R : Matrix ι ι ℂ) (α v β t : ℂ) (x y e : ι → ℂ)
    (hv : v^2=1) (hβ : β=1-α^2) (hβ0 : β≠0) (ht : β*t=α^2)
    (hleft : R*(1+t • (S*S))=1)
    (hx : x+α • (S.mulVec y+v • y)=e)
    (hy : y+α • (-S.mulVec x+v • x)=e) :
    x+y=(2/(1+v*α)) • R.mulVec e := by
  obtain ⟨hs,hd⟩ := sum_difference_equations S α v x y e hx hy
  have hfac : (1+v*α)*(1-v*α)=β := by
    rw [hβ]
    linear_combination -(α^2)*hv
  have ha : 1+v*α≠0 := by
    intro h
    rw [h,zero_mul] at hfac
    exact hβ0 hfac.symm
  have helim : β • (x+y)+α^2 • S.mulVec (S.mulVec (x+y))=
      (2*(1-v*α)) • e := by
    calc
      _ = (1-v*α) • ((1+v*α) • (x+y)-α • S.mulVec (x-y))+
          α • S.mulVec ((1-v*α) • (x-y)+α • S.mulVec (x+y)) := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
        rw [← hfac]
        module
      _ = _ := by rw [hs,hd,Matrix.mulVec_zero,smul_zero,add_zero]; module
  have hA : β • ((1+t • (S*S)).mulVec (x+y))=(2*(1-v*α)) • e := by
    simpa only [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec,smul_add,smul_smul,ht] using helim
  have hscaled := congrArg (fun b : ι → ℂ => β⁻¹ • b) hA
  have hsol : (1+t • (S*S)).mulVec (x+y)=(2/(1+v*α)) • e := by
    have hcoef : β⁻¹*(2*(1-v*α))=2/(1+v*α) := by
      apply (eq_div_iff ha).mpr
      calc
        _ = (β⁻¹*β)*2 := by rw [← hfac]; ring
        _ = 2 := by rw [inv_mul_cancel₀ hβ0,one_mul]
    simpa only [smul_smul,inv_mul_cancel₀ hβ0,one_smul,hcoef] using hscaled
  have h := congrArg (fun b => R.mulVec b) hsol
  simpa only [Matrix.mulVec_mulVec,hleft,Matrix.one_mulVec,Matrix.mulVec_smul] using h

/-- The block-system input uses the actual concatenated solution (x,y), not
assumed sum/difference equations. -/
theorem eliminate_block (S R : Matrix ι ι ℂ) (α v β t : ℂ) (x y e : ι → ℂ)
    (hv : v^2=1) (hβ : β=1-α^2) (hβ0 : β≠0) (ht : β*t=α^2)
    (hleft : R*(1+t • (S*S))=1)
    (hblock : (blockSystem S α v).mulVec (Sum.elim x y)=Sum.elim e e) :
    x+y=(2/(1+v*α)) • R.mulVec e := by
  have hx := congrArg (fun f : ι ⊕ ι → ℂ => f ∘ Sum.inl) hblock
  have hy := congrArg (fun f : ι ⊕ ι → ℂ => f ∘ Sum.inr) hblock
  simp only [blockSystem,Matrix.fromBlocks_mulVec,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    Matrix.one_mulVec,Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.neg_mulVec] at hx hy
  apply eliminate S R α v β t x y e hv hβ hβ0 ht hleft hx
  simpa only [add_comm] using hy

end BlockGaussianSourceElimination
#print axioms BlockGaussianSourceElimination.eliminate_block
