import AffineWickWord
import LinearSourceExpansion

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PartialMatchingAffine
open OccurrenceWickPolynomial FinitePairingTransport
variable {I V R : Type*} [Fintype I] [Fintype V] [CommSemiring R]

abbrev PartialPairing (V : Type*) := Σs : Finset V,Pairing s

instance : Fintype (PartialPairing V) := inferInstanceAs (Fintype (Σs : Finset V,Pairing s))

def weight (W : I → I → R) (hs : ∀i j,W i j=W j i) (eta : I → R) (a : V → I)
    (p : PartialPairing V) : R :=
  (∏x∈Finset.univ \ p.1,eta (a x))*
    SymmetricPairingTransport.weight (fun x y : p.1 => W (a x) (a y)) (fun x y => hs _ _) p.2

def total (W : I → I → R) (hs : ∀i j,W i j=W j i) (eta : I → R) (a : V → I) : R :=
  ∑p : PartialPairing V,weight W hs eta a p

theorem total_eq (W : I → I → R) (hs : ∀i j,W i j=W j i) (eta : I → R) (a : V → I) :
    total W hs eta a = ∑s : Finset V,(∏x∈Finset.univ \ s,eta (a x))*
      SymmetricPairingTransport.moment (fun x y : s => W (a x) (a y)) (fun x y => hs _ _) := by
  simp only [total,Fintype.sum_sigma,weight,SymmetricPairingTransport.moment,Finset.mul_sum]

theorem subset_wick (W : I → I → R) (hs : ∀i j,W i j=W j i) (a : V → I) (s : Finset V) :
    wick W hs (∏x∈s,MvPolynomial.X (a x))=
      SymmetricPairingTransport.moment (fun x y : s => W (a x) (a y)) (fun x y => hs _ _) := by
  rw [← Finset.prod_coe_sort]
  have hp := LinearSourceExpansion.product_monomial (S:=R) (fun _ : I => 1) (fun x : s => a x)
  simp only [one_smul,Finset.prod_const_one] at hp
  rw [hp,wick_monomial,one_mul,LinearSourceOccurrences.moment_assignment]

theorem affine_identity (W : I → I → R) (hs : ∀i j,W i j=W j i) (eta : I → R) (a : V → I) :
    wick W hs (∏x : V,(MvPolynomial.X (a x)+MvPolynomial.C (eta (a x))))=total W hs eta a := by
  rw [Finset.prod_add,map_sum,total_eq]
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro s hs'
  rw [← map_prod]
  have hh : (∏x∈s,MvPolynomial.X (a x))*MvPolynomial.C (∏x∈Finset.univ \ s,eta (a x))=
      (∏x∈Finset.univ \ s,eta (a x)) • (∏x∈s,MvPolynomial.X (a x)) := by
    rw [MvPolynomial.smul_eq_C_mul,mul_comm]
  rw [hh,map_smul,smul_eq_mul,subset_wick]

end PartialMatchingAffine
#print axioms PartialMatchingAffine.affine_identity
