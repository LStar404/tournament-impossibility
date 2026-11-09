import ResidualLogarithm

noncomputable section
namespace ResidualLogFiniteVertices
open ResidualLogarithm
variable {S : Type*} [Field S] [CharZero S] [Algebra ℚ S]

def shiftedLogarithm : PowerSeries S := PowerSeries.mk (fun k => (-1:S)^k/(k+3:S))

theorem logarithm_shift : logarithm (S:=S)=PowerSeries.X^3*shiftedLogarithm (S:=S) := by
  ext n
  rw [PowerSeries.coeff_X_pow_mul']
  rcases n with _ | n
  · simp [logarithm]
  rcases n with _ | n
  · simp [logarithm]
  rcases n with _ | n
  · simp [logarithm]
  simp [logarithm,shiftedLogarithm,Nat.add_assoc]

theorem power_below (b n : ℕ) (hn : n < 3*b) :
    ((logarithm (S:=S))^b).coeff n=0 := by
  rw [logarithm_shift,mul_pow,← pow_mul,PowerSeries.coeff_X_pow_mul']
  simp [show ¬3*b ≤ n by omega]

/-- Genuine scalar residual coefficients as a finite structural-vertex expansion. -/
theorem finite_exponential (n : ℕ) :
    (FactorizedResidualIdentity.residual (S:=S) (1:S)).coeff n =
      ∑b∈Finset.range (n/3+1),((1/(b.factorial:S))*((logarithm (S:=S))^b).coeff n) := by
  rw [actual_exp_identity,PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' constant_logarithm)]
  have hh : Function.support (fun b : ℕ => (PowerSeries.exp S).coeff b •
      ((logarithm (S:=S))^b).coeff n) ⊆ (Finset.range (n/3+1) : Set ℕ) := by
    intro b hb
    by_contra hn
    have hbn : n < 3*b := by
      have hnot : ¬ b < n/3+1 := by simpa using hn
      omega
    have hz := power_below (S:=S) b n hbn
    exact hb (by dsimp; rw [hz,mul_zero])
  rw [finsum_eq_sum_of_support_subset _ hh]
  apply Finset.sum_congr rfl
  intro b hb
  simp [PowerSeries.coeff_exp,smul_eq_mul]

theorem finite_vertices (n : ℕ) :
    (FactorizedResidualIdentity.residual (S:=S) (1:S)).coeff n =
      ∑b∈Finset.range (n/3+1),(1/(b.factorial:S))*
        (∑d∈Finset.finsuppAntidiag (Finset.range b) n,
          ∏v∈Finset.range b,(logarithm (S:=S)).coeff (d v)) := by
  rw [finite_exponential]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  exact PowerSeries.coeff_pow _ _ _

end ResidualLogFiniteVertices
#print axioms ResidualLogFiniteVertices.finite_vertices
