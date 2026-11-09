import PolynomialTiltedRecurrence

noncomputable section
namespace EvenUnitResidualDescent
variable {S : Type*} [Field S]

/-- Extracted from the actual residual, not defined as the desired quotient. -/
def extract (T : PowerSeries S) : PowerSeries S := PowerSeries.mk (fun k => T.coeff (2*k))

theorem reconstruction (F C T : PowerSeries S) (hc : C.constantCoeff=1)
    (h : PowerSeries.expand 2 (by decide) F = PowerSeries.expand 2 (by decide) C*T) :
    PowerSeries.expand 2 (by decide) (C⁻¹*F)=T := by
  have hi : C*C⁻¹=1 := PowerSeries.mul_inv_cancel _ (by rw [hc]; exact one_ne_zero)
  have he : PowerSeries.expand 2 (by decide) C * PowerSeries.expand 2 (by decide) (C⁻¹*F) =
      PowerSeries.expand 2 (by decide) C*T := by
    rw [← map_mul,← mul_assoc,hi,one_mul,h]
  have hz : (PowerSeries.expand 2 (by decide) C).constantCoeff ≠ 0 := by simpa using (show C.constantCoeff ≠ 0 by rw [hc]; exact one_ne_zero)
  have hh := congrArg (fun x => (PowerSeries.expand 2 (by decide) C)⁻¹*x) he
  have hu : (PowerSeries.expand 2 (by decide) C)⁻¹*PowerSeries.expand 2 (by decide) C=1 := by
    rw [mul_comm]; exact PowerSeries.mul_inv_cancel _ hz
  simpa only [← mul_assoc,hu,one_mul] using hh

theorem extract_formula (F C T : PowerSeries S) (hc : C.constantCoeff=1)
    (h : PowerSeries.expand 2 (by decide) F = PowerSeries.expand 2 (by decide) C*T) :
    extract T=C⁻¹*F := by
  ext k
  simp only [extract,PowerSeries.coeff_mk,← reconstruction F C T hc h,
    PowerSeries.coeff_expand_mul]

theorem actual_reconstruction (F C T : PowerSeries S) (hc : C.constantCoeff=1)
    (h : PowerSeries.expand 2 (by decide) F = PowerSeries.expand 2 (by decide) C*T) :
    PowerSeries.expand 2 (by decide) (extract T)=T := by
  rw [extract_formula F C T hc h]
  exact reconstruction F C T hc h

theorem factorization (F C T : PowerSeries S) (hc : C.constantCoeff=1)
    (h : PowerSeries.expand 2 (by decide) F = PowerSeries.expand 2 (by decide) C*T) :
    F=C*extract T := by
  rw [extract_formula F C T hc h,← mul_assoc,
    PowerSeries.mul_inv_cancel _ (by rw [hc]; exact one_ne_zero),one_mul]

theorem odd_zero (F C T : PowerSeries S) (hc : C.constantCoeff=1)
    (h : PowerSeries.expand 2 (by decide) F = PowerSeries.expand 2 (by decide) C*T) (k : ℕ) :
    T.coeff (2*k+1)=0 := by
  rw [← actual_reconstruction F C T hc h]
  apply PowerSeries.coeff_expand_of_not_dvd
  omega

end EvenUnitResidualDescent
#print axioms EvenUnitResidualDescent.factorization
