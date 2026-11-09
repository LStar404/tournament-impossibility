import StructuralPartialMatchingCounts

noncomputable section
attribute [local instance] Classical.typeDecidableEq
attribute [local instance] Classical.propDecidable
namespace PairingEdgeCard
open FinitePairingTransport SymmetricPairingTransport
variable {V : Type*} [Fintype V]

theorem graph_edges (p : Pairing V) : (PairingMomentParity.graph p).edgeFinset=edges p := by
  ext b
  induction b using Sym2.ind with
  | _ x y =>
    erw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change p.val x=y ↔ _
    simp only [edges, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨x,by rw [h]⟩
    · rintro ⟨w,hw⟩
      rcases Sym2.eq_iff.mp hw with h | h
      · rcases h with ⟨rfl,rfl⟩; rfl
      · rcases h with ⟨rfl,rfl⟩; exact p.property.1 _

theorem twice_card (p : Pairing V) : 2*(edges p).card=Fintype.card V := by
  have hd (x : V) : (PairingMomentParity.graph p).degree x=1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    refine ⟨p.val x,rfl,?_⟩
    intro y hy
    change p.val x=y at hy
    exact hy.symm
  have h := (PairingMomentParity.graph p).sum_degrees_eq_twice_card_edges
  rw [graph_edges] at h
  simpa only [hd,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using h.symm

theorem partial_card (p : PartialMatchingAffine.PartialPairing V) :
    (edges p.2).card=StructuralPartialMatchingCounts.pairCount p := by
  have h := twice_card p.2
  simp only [Fintype.card_coe] at h
  dsimp [StructuralPartialMatchingCounts.pairCount]
  omega
end PairingEdgeCard
#print axioms PairingEdgeCard.partial_card
