import PartialMatchingAffine

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PhysicalPartialMatching
open PhysicalTiltedCovariance OccurrenceWordDerivative
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem covariance_symmetry (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (i j : I) : covariance K A i j=covariance K A j i := by
  ext k
  have hh : PowerSeries.expand 2 (by decide) (covariance K A i j)=
      PowerSeries.expand 2 (by decide) (covariance K A j i) := by
    rw [expand_covariance,expand_covariance,MixedCovarianceSymmetry.covariance_symm K A hK hA i j]
  have hc := congrArg (fun F : PowerSeries S => F.coeff (2*k)) hh
  simpa only [PowerSeries.coeff_expand_mul] using hc

theorem affine_eq_physical (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (w : List I) :
    AffineWickWord.moment (covariance K A) (covariance_symmetry K A hK hA) (mean K A h) w=
      PhysicalWordEvenDescent.moment K A h w := by
  induction w using (measure (fun w : List I => w.length)).wf.induction with
  | h w ih =>
    cases w with
    | nil => erw [AffineWickWord.empty,PhysicalWordEvenDescent.moment_nil]
    | cons i w =>
      erw [AffineWickWord.recurrence,PhysicalWordEvenDescent.moment_cons,
        ih w (by change w.length < (i::w).length; simp)]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [ih p.2 (by change p.2.length < (i::w).length
                     have hh := deletion_length w p hp
                     simp only [List.length_cons]; omega)]

theorem polynomial_fin {R : Type*} [CommSemiring R] (eta : I → R) (w : List I) :
    AffineWickWord.polynomial eta w =
      ∏x : Fin w.length,(MvPolynomial.X (w.get x)+MvPolynomial.C (eta (w.get x))) := by
  have hh : AffineWickWord.polynomial eta w=
      (w.map (fun i => MvPolynomial.X i+MvPolynomial.C (eta i))).prod := by
    induction w with
    | nil => rfl
    | cons i w ih => simp [AffineWickWord.polynomial,ih]
  rw [hh]
  conv_lhs => rw [← List.ofFn_get w,List.map_ofFn,List.prod_ofFn]
  rfl

theorem actual_matching (K A : I → I → S) (hK : ∀i j,K i j=K j i)
    (hA : ∀i j,A i j=A j i) (h : I → S) (w : List I) :
    PhysicalWordEvenDescent.moment K A h w=
      PartialMatchingAffine.total (covariance K A) (covariance_symmetry K A hK hA)
        (mean K A h) w.get := by
  rw [← affine_eq_physical K A hK hA]
  unfold AffineWickWord.moment
  rw [polynomial_fin]
  exact PartialMatchingAffine.affine_identity _ _ _ _

end PhysicalPartialMatching
#print axioms PhysicalPartialMatching.actual_matching
