import WeightedCoefficientProducts
import PhysicalActivityOrder

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PartialMatchingWeightedBound
open WeightedCoefficientNorm PartialMatchingAffine StructuralPartialMatchingCounts
variable {I V : Type*} [Fintype V]

theorem bound (W : I → I → PowerSeries ℂ) (hs : ∀i j,W i j=W j i)
    (eta : I → PowerSeries ℂ) (a : V → I) (p : PartialPairing V)
    {rho B E : ℝ} (hr : 0≤rho) (hB : 0≤B) (hE : 0≤E)
    (hW : ∀i j,Finite rho (W i j)) (he : ∀i,Finite rho (eta i))
    (bW : ∀i j,norm rho (W i j)≤B) (be : ∀i,norm rho (eta i)≤E) :
    Finite rho (weight W hs eta a p) ∧
      norm rho (weight W hs eta a p)≤B^(pairCount p)*E^(singletonCount p) := by
  let f : Sym2 p.1 → PowerSeries ℂ :=
    Sym2.lift ⟨(fun x y : p.1 => W (a x) (a y)),fun x y => hs _ _⟩
  have hf (b : Sym2 p.1) : Finite rho (f b) := by
    induction b using Sym2.ind with
    | _ x y => exact hW _ _
  have bf (b : Sym2 p.1) : norm rho (f b)≤B := by
    induction b using Sym2.ind with
    | _ x y => exact bW _ _
  have hm := WeightedCoefficientProducts.product (Finset.univ \ p.1) (fun x => eta (a x)) hr
    (fun x hx => he _)
  have hp := WeightedCoefficientProducts.product (SymmetricPairingTransport.edges p.2) f hr
    (fun x hx => hf x)
  have bm := WeightedCoefficientProducts.product_bound (Finset.univ \ p.1) (fun x => eta (a x))
    hr hE (fun x hx => he _) (fun x hx => be _)
  have bp := WeightedCoefficientProducts.product_bound (SymmetricPairingTransport.edges p.2) f
    hr hB (fun x hx => hf x) (fun x hx => bf x)
  rw [PairingEdgeCard.partial_card] at bp
  change Finite rho ((∏x∈Finset.univ \ p.1,eta (a x))*∏x∈SymmetricPairingTransport.edges p.2,f x) ∧ _
  constructor
  · exact finite_mul hr hm.1 hp.1
  · apply (mul_bound hr hm.1 hp.1).trans
    have hh := mul_le_mul bm bp (norm_nonnegative hr _) (pow_nonneg hE _)
    simpa only [singletonCount,mul_comm] using hh

/-- Sum over unrestricted structural labels uses |I|^b, not |I|^D. -/
theorem labels [Fintype I] {b : ℕ} (d : Fin b → ℕ) (p : PartialPairing (Positions d))
    (W : I → I → PowerSeries ℂ) (hs : ∀i j,W i j=W j i) (eta : I → PowerSeries ℂ)
    {rho B E : ℝ} (hr : 0≤rho) (hB : 0≤B) (hE : 0≤E)
    (hW : ∀i j,Finite rho (W i j)) (he : ∀i,Finite rho (eta i))
    (bW : ∀i j,norm rho (W i j)≤B) (be : ∀i,norm rho (eta i)≤E) :
    (∑a : Fin b → I,norm rho (weight W hs eta (fun x : Positions d => a x.1) p)) ≤
      (Fintype.card I:ℝ)^b*(B^(pairCount p)*E^(singletonCount p)) := by
  calc
    _ ≤ ∑a : Fin b → I,B^(pairCount p)*E^(singletonCount p) :=
      Finset.sum_le_sum (fun a ha => (bound W hs eta _ p hr hB hE hW he bW be).2)
    _ = _ := by simp [Fintype.card_fun]
end PartialMatchingWeightedBound
#print axioms PartialMatchingWeightedBound.labels
