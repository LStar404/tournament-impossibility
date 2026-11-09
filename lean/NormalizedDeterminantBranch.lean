import MixedWardUnit
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution

noncomputable section
namespace NormalizedDeterminantBranch
variable {S : Type*} [Field S] [CharZero S] [Algebra ℚ S]

def universal : PowerSeries S := PowerSeries.binomialSeries S (-1/2:ℚ)

theorem universal_square : (universal (S:=S))^2 * (1+PowerSeries.X) = 1 := by
  have h1 : PowerSeries.binomialSeries S (1:ℚ) = 1+PowerSeries.X := by
    simpa using (PowerSeries.binomialSeries_nat (R:=ℚ) (A:=S) 1)
  rw [universal, pow_two, ← h1, ← PowerSeries.binomialSeries_add, ← PowerSeries.binomialSeries_add]
  norm_num

def branch (d : PowerSeries S) : PowerSeries S :=
  PowerSeries.subst (d-1) (universal (S:=S))

theorem branch_square (d : PowerSeries S) (hd : d.constantCoeff=1) :
    (branch d)^2 * d = 1 := by
  have hz : (d-1).constantCoeff=0 := by simp [hd]
  let φ : PowerSeries S →ₐ[S] PowerSeries S :=
    PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hz)
  have hh := congrArg φ (universal_square (S:=S))
  simp only [map_mul, map_pow, map_add, map_one, PowerSeries.substAlgHom_X] at hh
  simpa [φ, PowerSeries.coe_substAlgHom, branch,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hz)] using hh

theorem branch_constant (d : PowerSeries S) (hd : d.constantCoeff=1) :
    (branch d).constantCoeff=1 := by
  have hz : (d-1).constantCoeff=0 := by simp [hd]
  change MvPowerSeries.constantCoeff (PowerSeries.subst (d-1) (universal (S:=S))) = 1
  rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hz]
  simp [universal]

end NormalizedDeterminantBranch
#print axioms NormalizedDeterminantBranch.branch_square
#print axioms NormalizedDeterminantBranch.branch_constant
