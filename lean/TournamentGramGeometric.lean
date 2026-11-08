import TournamentEnergyRowDomain
noncomputable section
namespace TournamentGramGeometric
open Finset Matrix VectorWeakMajorization TournamentPowerComparison TournamentEnergyRowDomain

def gram {n : ℕ} (B : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  (matrix B).transpose * matrix B

def C {n : ℕ} (B : Tournament n) (q : ℝ) : Matrix (Fin n) (Fin n) ℝ := q • gram B

lemma transpose_matrix {n : ℕ} (B : Tournament n) : (matrix B).transpose = -(matrix B) := by
  ext i j
  exact B.skew j i

lemma C_action {n : ℕ} (B : Tournament n) (q : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (C B q).mulVec x i = -(q * B.act (B.act x) i) := by
  unfold C gram
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, transpose_matrix, Matrix.neg_mulVec]
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  change q * (-(B.act (B.act x) i)) = _
  ring

lemma C_action_bound {n : ℕ} (B : Tournament n) (q : ℝ) (hq : 0 ≤ q)
    (x : Fin n → ℝ) (M : ℝ) (hx : ∀ j, |x j| ≤ M) (i : Fin n) :
    |(C B q).mulVec x i| ≤ (q*rowBase n ^2)*M := by
  have hfirst := fun j => TournamentEnergyRowDomain.act_abs_le B x M hx j
  have hsecond := TournamentEnergyRowDomain.act_abs_le B (B.act x) (rowBase n*M) hfirst i
  rw [C_action, abs_neg, abs_mul, abs_of_nonneg hq]
  calc
    _ ≤ q*(rowBase n*(rowBase n*M)) := mul_le_mul_of_nonneg_left hsecond hq
    _ = _ := by ring

lemma power_basis_bound {n : ℕ} (B : Tournament n) (q : ℝ) (hq : 0 ≤ q)
    (r : ℕ) (j i : Fin n) :
    |((C B q)^r).mulVec (basis j) i| ≤ (q*rowBase n ^2)^r := by
  induction r generalizing i with
  | zero =>
    by_cases hij : i=j <;> simp [basis, Matrix.one_apply, hij]
  | succ r ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    have h := C_action_bound B q hq (((C B q)^r).mulVec (basis j))
      ((q*rowBase n ^2)^r) ih i
    simpa [pow_succ'] using h

lemma power_entry_bound {n : ℕ} (B : Tournament n) (q : ℝ) (hq : 0 ≤ q)
    (r : ℕ) (i j : Fin n) : |((C B q)^r) i j| ≤ (q*rowBase n ^2)^r := by
  simpa [basis] using power_basis_bound B q hq r j i

/-- The full matrix geometric series, not merely a scalar-energy series,
is summable on the proved finite row-sum domain. -/
theorem geometric_summable {n : ℕ} (B : Tournament n) (q : ℝ)
    (hq : 0 ≤ q) (hsmall : q*rowBase n ^2 < 1) : Summable (fun r : ℕ => (C B q)^r) := by
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  apply (summable_geometric_of_lt_one (mul_nonneg hq (sq_nonneg _)) hsmall).of_norm_bounded
  intro r
  simpa only [Real.norm_eq_abs] using power_entry_bound B q hq r i j
end TournamentGramGeometric
#print axioms TournamentGramGeometric.geometric_summable
