import GlobalResidualLog

noncomputable section
namespace GlobalLogFiniteVertices
open GlobalResidualLog ZeroConstantFormalExp
variable {I S P : Type*} [Fintype I] [Field S] [CharZero S] [Algebra ℚ S]
    [CommRing P] [Algebra S P] [Algebra ℚ P]

theorem local_shift (a : P) : ∃H : PowerSeries P,localLog (S:=S) a=PowerSeries.X^3*H := by
  unfold localLog
  rw [ResidualLogFiniteVertices.logarithm_shift,map_mul,map_pow,PowerSeries.map_X,
    map_mul,map_pow,PowerSeries.rescale_X,mul_pow]
  refine ⟨PowerSeries.C a^3 * PowerSeries.rescale a
    (PowerSeries.map (algebraMap S P) (ResidualLogFiniteVertices.shiftedLogarithm (S:=S))),?_⟩
  ring

theorem global_shift (a : I → P) : ∃H : PowerSeries P,
    (∑i,localLog (S:=S) (a i))=PowerSeries.X^3*H := by
  classical
  choose H hH using fun i => local_shift (S:=S) (a i)
  refine ⟨∑i,H i,?_⟩
  simp only [hH,Finset.mul_sum]

theorem power_below (a : I → P) (b m : ℕ) (hm : m < 3*b) :
    ((∑i,localLog (S:=S) (a i))^b).coeff m=0 := by
  obtain ⟨H,hH⟩ := global_shift (S:=S) a
  rw [hH,mul_pow,← pow_mul,PowerSeries.coeff_X_pow_mul']
  simp [show ¬3*b ≤ m by omega]

theorem finite_coefficient (a : I → P) (m : ℕ) :
    (∏i,FactorizedResidualIdentity.residual (S:=S) (a i)).coeff m =
      ∑b∈Finset.range (m/3+1),algebraMap ℚ P (1/(b.factorial:ℚ))*
        ((∑i,localLog (S:=S) (a i))^b).coeff m := by
  classical
  rw [finite_identity]
  unfold expOf
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by
    simp only [map_sum]; exact Finset.sum_eq_zero (fun i hi => local_constant _)))]
  have hh : Function.support (fun b : ℕ => (PowerSeries.exp P).coeff b •
      ((∑i,localLog (S:=S) (a i))^b).coeff m) ⊆ (Finset.range (m/3+1) : Set ℕ) := by
    intro b hb
    by_contra hn
    have hbm : m < 3*b := by
      have hnot : ¬b < m/3+1 := by simpa using hn
      omega
    exact hb (by dsimp; rw [power_below a b m hbm,mul_zero])
  rw [finsum_eq_sum_of_support_subset _ hh]
  apply Finset.sum_congr rfl
  intro b hb
  simp [PowerSeries.coeff_exp,smul_eq_mul]

theorem ordered_vertices (a : I → P) (m : ℕ) :
    (∏i,FactorizedResidualIdentity.residual (S:=S) (a i)).coeff m =
      ∑b∈Finset.range (m/3+1),algebraMap ℚ P (1/(b.factorial:ℚ))*
        (∑label : Fin b → I, (∏v,localLog (S:=S) (a (label v))).coeff m) := by
  rw [finite_coefficient]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Fintype.sum_pow,map_sum]
end GlobalLogFiniteVertices
#print axioms GlobalLogFiniteVertices.ordered_vertices
