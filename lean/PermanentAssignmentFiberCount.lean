import PermanentLinearProductIntegral
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Basic
noncomputable section
namespace PermanentPositiveMoments
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
abbrev MatchingPerm (a b : J → I) := {s : Equiv.Perm J // ∀i, a (s i)=b i}

def fiberMatchingEquiv (a b : J → I) : MatchingPerm a b ≃
    (∀l, {i // b i=l} ≃ {i // a i=l}) where
  toFun s l := s.val.subtypeEquiv (fun i => by rw [s.property i])
  invFun e := ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩
  left_inv s := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    rfl
  right_inv e := by
    funext l
    apply Equiv.ext
    intro i
    apply Subtype.ext
    change ((e (b i.val)) ⟨i.val,rfl⟩).val = (e l i).val
    rcases i with ⟨i, hi⟩
    subst l
    rfl

lemma multiplicity_card (a : J → I) (l : I) :
    multiplicity a l = Fintype.card {i // a i=l} := by
  simp [multiplicity, Fintype.card_subtype]

theorem matchingPerm_count (a b : J → I) :
    Fintype.card (MatchingPerm a b) =
      if multiplicity a=multiplicity b then ∏l, (multiplicity a l).factorial else 0 := by
  classical
  rw [Fintype.card_congr (fiberMatchingEquiv a b), Fintype.card_pi]
  by_cases hab : multiplicity a=multiplicity b
  · rw [if_pos hab]
    apply Finset.prod_congr rfl
    intro l hl
    have hc : Fintype.card {i // b i=l}=Fintype.card {i // a i=l} := by
      rw [← multiplicity_card, ← multiplicity_card, hab]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq hc), ← multiplicity_card, ← hab]
  · rw [if_neg hab]
    obtain ⟨l,hl⟩ := Function.ne_iff.mp hab
    apply Finset.prod_eq_zero (Finset.mem_univ l)
    letI : IsEmpty ({i // b i=l} ≃ {i // a i=l}) := ⟨fun e => hl (by
      rw [multiplicity_card, multiplicity_card]
      exact (Fintype.card_congr e).symm)⟩
    exact Fintype.card_eq_zero
end PermanentPositiveMoments
#print axioms PermanentPositiveMoments.matchingPerm_count
