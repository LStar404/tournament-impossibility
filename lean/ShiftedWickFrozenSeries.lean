import FrozenSeriesGrouping
import FullWickSquarefreeCompatibility
import FactorizedResidualIdentity

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace ShiftedWickFrozenSeries
open FormalLinearLift OccurrenceWickPolynomial FullWickSquarefreeCompatibility
open FrozenSeriesGrouping SubsetPairingScaling
variable {S : Type*} [Field S] [CharZero S]

theorem lift_sum {P J : Type*} [CommRing P] [Algebra S P]
    (f : P →ₗ[S] S) (s : Finset J) (F : J → PowerSeries P) :
    lift f (∑j∈s,F j)=∑j∈s,lift f (F j) := by ext n; simp

theorem lift_monomial {P : Type*} [CommRing P] [Algebra S P]
    (f : P →ₗ[S] S) (p : P) (m : ℕ) :
    lift f (PowerSeries.C p*PowerSeries.X^m)=PowerSeries.C (f p)*PowerSeries.X^m := by
  ext n
  simp only [coeff_lift,PowerSeries.coeff_C_mul_X_pow]
  split_ifs <;> simp

theorem subset_product {n : ℕ} (I J : Finset (Fin n)) :
    (∏i∈I,PowerSeries.C (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin n ⊕ Fin n) S)*PowerSeries.X)*
    (∏j∈J,PowerSeries.C (MvPolynomial.X (Sum.inr j))*PowerSeries.X) =
      PowerSeries.C (MvPolynomial.monomial (SquarefreePairingContraction.exponent I J) 1)*
        PowerSeries.X^(I.card+J.card) := by
  simp only [Finset.prod_mul_distrib,Finset.prod_const,← map_prod,← mul_pow]
  rw [pow_add,← SquarefreePairingContraction.product_monomial, map_mul]
  ring

theorem shifted_identity {n : ℕ} (M : Matrix (Fin n) (Fin n) S) :
    lift (wick (block M) (block_symm M)) (FactorizedResidualIdentity.shiftedProduct (S:=S)) =
      PowerSeries.expand 2 (by decide) (series M) := by
  unfold FactorizedResidualIdentity.shiftedProduct
  rw [ShiftedProductSubsetExpansion.split_product]
  simp_rw [lift_sum,subset_product,lift_monomial,wick_monomial,
    monomialMoment_eq,one_mul,degree_weight]
  rw [weighted_group M (fun k => PowerSeries.X^(2*k))]
  simp [series,PowerSeries.expand_C,pow_mul]

end ShiftedWickFrozenSeries
#print axioms ShiftedWickFrozenSeries.shifted_identity
