import PairingEdgeCard
import PhysicalPartialMatching

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PartialMatchingWeightOrder
open PartialMatchingAffine StructuralPartialMatchingCounts
variable {S : Type*} [CommRing S]

theorem prod_divisible {J : Type*} (s : Finset J) (f : J → PowerSeries S)
    (h : ∀j∈s,(f j).constantCoeff=0) :
    (PowerSeries.X : PowerSeries S)^s.card ∣ ∏j∈s,f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha,Finset.prod_insert ha,pow_succ']
    exact mul_dvd_mul (PowerSeries.X_dvd_iff.mpr (h a (by simp)))
      (ih (fun j hj => h j (by simp [hj])))

theorem divisible {I V : Type*} [Fintype V]
    (W : I → I → PowerSeries S) (hs : ∀i j,W i j=W j i)
    (eta : I → PowerSeries S) (a : V → I) (p : PartialPairing V)
    (hW : ∀i j,(W i j).constantCoeff=0) (he : ∀i,(eta i).constantCoeff=0) :
    (PowerSeries.X : PowerSeries S)^(pairCount p+singletonCount p) ∣
      weight W hs eta a p := by
  have hm := prod_divisible (Finset.univ \ p.1) (fun x => eta (a x))
    (fun x hx => he _)
  have hp := prod_divisible (SymmetricPairingTransport.edges p.2)
    (fun b => Sym2.lift ⟨(fun x y : p.1 => W (a x) (a y)),(fun x y => hs _ _)⟩ b)
    (by
      intro b hb
      induction b using Sym2.ind with
      | _ x y => simpa only [Sym2.lift_mk] using hW (a x) (a y))
  rw [PairingEdgeCard.partial_card] at hp
  simpa only [pow_add,weight,SymmetricPairingTransport.weight,singletonCount,
    mul_comm] using mul_dvd_mul hm hp

theorem below {I V : Type*} [Fintype V]
    (W : I → I → PowerSeries S) (hs : ∀i j,W i j=W j i)
    (eta : I → PowerSeries S) (a : V → I) (p : PartialPairing V)
    (hW : ∀i j,(W i j).constantCoeff=0) (he : ∀i,(eta i).constantCoeff=0)
    (k : ℕ) (hk : k < pairCount p+singletonCount p) :
    (weight W hs eta a p).coeff k=0 := by
  obtain ⟨F,hF⟩ := divisible W hs eta a p hW he
  rw [hF,PowerSeries.coeff_X_pow_mul']
  simp [show ¬pairCount p+singletonCount p ≤ k by omega]
end PartialMatchingWeightOrder
#print axioms PartialMatchingWeightOrder.below
