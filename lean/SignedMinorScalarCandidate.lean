import MinorNormalizationCandidate
set_option autoImplicit false
noncomputable section
namespace SignedMinorScalarCandidate

/-- Signed lower bound: the target bracket may be negative. -/
lemma signed_lower {P A G E d h : ℝ}
    (hG : 1≤G) (hh : 0≤h)
    (_hA0 : 0≤A) (hAl : Real.exp (-1-d)≤A) (hAu : A≤Real.exp 1)
    (hP : A*(G*Real.exp (-E)-h)≤P) :
    Real.exp (-1)*G*(1-(d+E+Real.exp 2*h))≤P := by
  have hG0 : 0≤G := by linarith
  have hmain : Real.exp (-1)*G*Real.exp (-(d+E))≤A*G*Real.exp (-E) := by
    have hh := mul_le_mul_of_nonneg_right hAl (mul_nonneg hG0 (Real.exp_pos (-E)).le)
    have he : Real.exp (-1-d)*(G*Real.exp (-E))=Real.exp (-1)*G*Real.exp (-(d+E)) := by
      rw [show -1-d=(-1)+(-d) by ring, Real.exp_add, show -(d+E)=(-d)+(-E) by ring, Real.exp_add]
      ring
    rw [he] at hh
    nlinarith only [hh]
  have hlin : 1-(d+E)≤Real.exp (-(d+E)) := by linarith [Real.add_one_le_exp (-(d+E))]
  have hlin' := mul_le_mul_of_nonneg_left hlin (mul_nonneg (Real.exp_pos (-1)).le hG0)
  have herr : A*h≤Real.exp (-1)*G*(Real.exp 2*h) := by
    have h1 := mul_le_mul_of_nonneg_right hAu hh
    have h2 := mul_le_mul_of_nonneg_right hG (mul_nonneg (Real.exp_pos 1).le hh)
    have he : Real.exp (-1)*Real.exp 2=Real.exp 1 := by rw [← Real.exp_add]; norm_num
    calc
      _ ≤ Real.exp 1*h := h1
      _ ≤ G*(Real.exp 1*h) := by simpa only [one_mul] using h2
      _ = _ := by rw [← he]; ring
  nlinarith only [hmain,hlin',herr,hP]
end SignedMinorScalarCandidate
