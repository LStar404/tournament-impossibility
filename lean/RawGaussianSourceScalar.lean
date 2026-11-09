import GaussianSourceExponent
import ActualGaussianSourceExponent

noncomputable section

/-! Exact scalar normalization only. No matrix source is defined to equal this
scalar: a separate block inverse argument must identify its contraction with
`reducedSource`. The branch interpretation requires v^2=1. -/
namespace RawGaussianSourceScalar
open DiamondGap

/-- Scalar obtained after the independently proved block/source contractions. -/
def reducedSource (n : ℕ) (v z k ψ : ℂ) : ℂ :=
  (n : ℂ) - ((n : ℂ) + (k / (n : ℂ)) ^ 2 * ψ) /
    (1 + v * (z / (n : ℂ)))

/-- The denominators cannot simply be omitted: complex division is totalized. -/
theorem reducedSource_eq_exponent (n : ℕ) (hn : 0 < n) (v z k ψ : ℂ)
    (hd : 1 + v * (z / (n : ℂ)) ≠ 0) :
    reducedSource n v z k ψ = GaussianSourceExponent.exponent n (v * z) k ψ := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hform : 1 + v * (z / (n : ℂ)) = 1 + (v * z) / (n : ℂ) := by ring
  have hd' : 1 + (v * z) / (n : ℂ) ≠ 0 := hform ▸ hd
  unfold reducedSource GaussianSourceExponent.exponent
  rw [hform]
  apply (mul_right_cancel₀ hd')
  simp only [sub_mul, div_mul_cancel₀ _ hd']
  field_simp [hnC]
  ring

/-- For the two actual sign branches beta nonzero supplies the denominator. -/
theorem denominator_ne_zero (α v : ℂ) (hv : v ^ 2 = 1)
    (hβ : 1 - α ^ 2 ≠ 0) : 1 + v * α ≠ 0 := by
  have hprod : (1 + v * α) * (1 - v * α) = 1 - α ^ 2 := by
    calc
      _ = 1 - v ^ 2 * α ^ 2 := by ring
      _ = _ := by rw [hv]; ring
  intro h
  apply hβ
  rw [← hprod, h, zero_mul]

/-- Exact identification with the existing source expression, once the
matrix-level argument has reached reducedSource. This does not assert that
argument as a premise-free raw source equality. -/
theorem reducedSource_eq_actualExponent {n : ℕ} (hn : 0 < n)
    (T : Tournament (Fin n)) (v z : ℂ) (hv : v ^ 2 = 1)
    (hβ : GaussianParameterBranch.beta n z ≠ 0) :
    reducedSource n v z (GaussianParameterBranch.parameter n z)
      (ActualComplexScoreSource.source T (GaussianParameterBranch.parameter n z)) =
    ActualGaussianSourceExponent.actualExponent T v z := by
  apply reducedSource_eq_exponent n hn
  apply denominator_ne_zero (z / (n : ℂ)) v hv
  exact hβ

end RawGaussianSourceScalar
#print axioms RawGaussianSourceScalar.reducedSource_eq_exponent
#print axioms RawGaussianSourceScalar.reducedSource_eq_actualExponent
