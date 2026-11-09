import PhysicalWordEvenDescent

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PhysicalWordCoefficientOrder
open OccurrenceWordDerivative PhysicalWordRecurrence PhysicalWordEvenDescent
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

theorem coefficient_identity (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j,A i j=A j i) (w : List I) (k : ℕ) :
    (moment K A h w).coeff k = (physical K hs h A w).coeff (2*k) := by
  rw [← expand_moment K hs h A hA w,PowerSeries.coeff_expand_mul]

theorem physical_odd (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j,A i j=A j i) (w : List I) (k : ℕ) :
    (physical K hs h A w).coeff (2*k+1)=0 := by
  rw [← expand_moment K hs h A hA w]
  apply PowerSeries.coeff_expand_of_not_dvd
  omega

/-- True minimum z-order, derived from the actual physical u-scaling. -/
theorem coefficient_below_order (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j,A i j=A j i)
    (w : List I) (k : ℕ) (hk : 2*k < w.length) :
    (moment K A h w).coeff k=0 := by
  rw [coefficient_identity K hs h A hA,physical,PowerSeries.coeff_X_pow_mul']
  simp [show ¬w.length ≤ 2*k by omega]

theorem polynomial_prod (w : List I) :
    polynomial (S:=S) w = (w.map MvPolynomial.X).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [polynomial,ih]

theorem permutation (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j,A i j=A j i)
    (w v : List I) (hp : w.Perm v) : moment K A h w=moment K A h v := by
  have hpoly : polynomial (S:=S) w=polynomial v := by
    rw [polynomial_prod,polynomial_prod]
    exact (hp.map MvPolynomial.X).prod_eq
  ext k
  rw [coefficient_identity K hs h A hA,coefficient_identity K hs h A hA]
  simp only [physical,hp.length_eq,hpoly]

end PhysicalWordCoefficientOrder
#print axioms PhysicalWordCoefficientOrder.coefficient_below_order
#print axioms PhysicalWordCoefficientOrder.permutation
