import TournamentEnergySeries
noncomputable section
namespace ResolventSeriesIdentity
open Finset Matrix
variable {n : ℕ}

/-- Matrix Neumann identity from proved summability, with the actual
nonsingular matrix inverse rather than an abstract inverse parameter. -/
theorem inverse_eq_geometric (C : Matrix (Fin n) (Fin n) ℝ)
    (h : Summable (fun r : ℕ => C^r)) :
    (1-C)⁻¹ = ∑' r : ℕ, C^r := by
  exact Matrix.inv_eq_left_inv h.tsum_pow_mul_one_sub

/-- The inverse is genuine: both multiplication identities hold. -/
theorem inverse_left_right (C : Matrix (Fin n) (Fin n) ℝ)
    (h : Summable (fun r : ℕ => C^r)) :
    (1-C)⁻¹ * (1-C) = 1 ∧ (1-C) * (1-C)⁻¹ = 1 := by
  rw [inverse_eq_geometric C h]
  exact ⟨h.tsum_pow_mul_one_sub, h.one_sub_mul_tsum_pow⟩

lemma quadratic_hasSum (C : Matrix (Fin n) (Fin n) ℝ)
    (h : Summable (fun r : ℕ => C^r)) (b : Fin n → ℝ) :
    HasSum (fun r : ℕ => dotProduct b ((C^r).mulVec b))
      (dotProduct b ((∑' r : ℕ, C^r).mulVec b)) := by
  have he (i j : Fin n) :
      HasSum (fun r : ℕ => b i * ((C^r) i j * b j))
        (b i * ((∑' r : ℕ, C^r) i j * b j)) := by
    exact ((Pi.hasSum.mp (Pi.hasSum.mp h.hasSum i) j).mul_right (b j)).mul_left (b i)
  have hs := hasSum_sum (s := (univ : Finset (Fin n))) (fun i _ =>
    hasSum_sum (s := (univ : Finset (Fin n))) (fun j _ => he i j))
  simpa only [dotProduct, Matrix.mulVec, mul_sum] using hs

theorem quadratic_resolvent_eq_tsum (C : Matrix (Fin n) (Fin n) ℝ)
    (h : Summable (fun r : ℕ => C^r)) (b : Fin n → ℝ) :
    dotProduct b ((1-C)⁻¹.mulVec b) =
      ∑' r : ℕ, dotProduct b ((C^r).mulVec b) := by
  rw [inverse_eq_geometric C h]
  exact (quadratic_hasSum C h b).tsum_eq.symm

/-- The actual Gram-series coefficient is the all-one/source energy at r+1.
Normality is explicit here and discharged by skew symmetry in applications. -/
theorem source_coefficient (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Commute A.transpose A) (q : ℝ) (r : ℕ) :
    dotProduct (A.mulVec (fun _ => (1:ℝ)))
      (((q • (A.transpose*A))^r).mulVec (A.mulVec (fun _ => (1:ℝ)))) =
      q^r * TournamentEnergySeries.energy A (r+1) := by
  rw [smul_pow, Matrix.smul_mulVec, dotProduct_smul]
  change q^r * dotProduct (A.mulVec (fun _ => (1:ℝ)))
    (((A.transpose*A)^r).mulVec (A.mulVec (fun _ => (1:ℝ)))) = _
  rw [← SignedVectorOrbit.norm_sq_gram_power A hA r]
  simp only [Matrix.mulVec_mulVec, ← pow_succ]
  rfl

/-- Under summability the resolvent quadratic equals the source-energy series.
This theorem does not postulate the equality of its coefficients. -/
theorem source_resolvent_eq_series (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Commute A.transpose A) (q : ℝ)
    (h : Summable (fun r : ℕ => (q • (A.transpose*A))^r)) :
    dotProduct (A.mulVec (fun _ => (1:ℝ)))
      ((1-q • (A.transpose*A))⁻¹.mulVec (A.mulVec (fun _ => (1:ℝ)))) =
      ∑' r : ℕ, q^r * TournamentEnergySeries.energy A (r+1) := by
  rw [quadratic_resolvent_eq_tsum _ h]
  apply tsum_congr
  intro r
  exact source_coefficient A hA q r
end ResolventSeriesIdentity
#print axioms ResolventSeriesIdentity.inverse_eq_geometric
#print axioms ResolventSeriesIdentity.source_resolvent_eq_series
