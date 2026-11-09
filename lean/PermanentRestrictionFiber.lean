import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact completion multiplicity for a fixed restriction.
This file does not assume any coefficient identity. -/
noncomputable section
open scoped BigOperators
namespace PermanentRestrictionFiber

variable {n : ℕ} (I J : Finset (Fin n))
abbrev Outside (I : Finset (Fin n)) := {i : Fin n // i ∉ I}
def Fiber (p : I ≃ J) := {σ : Equiv.Perm (Fin n) // ∀ i : I, σ i = (p i : Fin n)}

instance fiberFintype (p : I ≃ J) : Fintype (Fiber I J p) := by
  classical
  unfold Fiber
  infer_instance

/-- Glue the prescribed restriction and an arbitrary complementary bijection. -/
def glue (p : I ≃ J) (q : Outside I ≃ Outside J) : Equiv.Perm (Fin n) :=
  (Equiv.sumCompl (fun i => i ∈ I)).symm |>.trans
    ((Equiv.sumCongr p q).trans (Equiv.sumCompl (fun j => j ∈ J)))

@[simp] lemma glue_inside (p : I ≃ J) (q : Outside I ≃ Outside J) (i : I) :
    glue I J p q i = (p i : Fin n) := by
  simp [glue]
@[simp] lemma glue_outside (p : I ≃ J) (q : Outside I ≃ Outside J)
    (i : Outside I) : glue I J p q i = (q i : Fin n) := by
  simp [glue]

lemma maps_outside (p : I ≃ J) (σ : Fiber I J p) (i : Outside I) :
    σ.val i ∉ J := by
  intro h
  let j : J := ⟨σ.val i, h⟩
  have he : σ.val (p.symm j) = σ.val i := by
    simpa [j] using σ.property (p.symm j)
  have hi : ((p.symm j : I) : Fin n) = i := σ.val.injective he
  exact i.property (hi ▸ (p.symm j).property)

lemma inv_maps_outside (p : I ≃ J) (σ : Fiber I J p) (j : Outside J) :
    σ.val.symm j ∉ I := by
  intro h
  have he := σ.property ⟨σ.val.symm j, h⟩
  have hj : (j : Fin n) = (p ⟨σ.val.symm j, h⟩ : Fin n) := by
    simpa using he
  exact j.property (hj.symm ▸ (p ⟨σ.val.symm j, h⟩).property)

def restrictOutside (p : I ≃ J) (σ : Fiber I J p) : Outside I ≃ Outside J where
  toFun i := ⟨σ.val i, maps_outside I J p σ i⟩
  invFun j := ⟨σ.val.symm j, inv_maps_outside I J p σ j⟩
  left_inv i := by apply Subtype.ext; exact σ.val.symm_apply_apply i
  right_inv j := by apply Subtype.ext; exact σ.val.apply_symm_apply j

/-- The restriction fiber is exactly the type of complementary bijections. -/
def fiberEquiv (p : I ≃ J) : Fiber I J p ≃ (Outside I ≃ Outside J) where
  toFun := restrictOutside I J p
  invFun q := ⟨glue I J p q, glue_inside I J p q⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ I
    · exact (glue_inside I J p (restrictOutside I J p σ) ⟨i, hi⟩).trans
        (σ.property ⟨i, hi⟩).symm
    · exact glue_outside I J p (restrictOutside I J p σ) ⟨i, hi⟩
  right_inv q := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    exact glue_outside I J p q i

theorem card_fiber (p : I ≃ J) : Fintype.card (Fiber I J p) = (n - I.card).factorial := by
  classical
  have hc : Fintype.card (Outside I) = Fintype.card (Outside J) :=
    Fintype.card_compl_eq_card_compl (fun i => i ∈ I) (fun j => j ∈ J)
      (Fintype.card_congr p)
  let e : Outside I ≃ Outside J := Fintype.equivOfCardEq hc
  rw [Fintype.card_congr (fiberEquiv I J p), Fintype.card_equiv e]
  simp [Outside]

/-- A weight depending only on the chosen restriction is constant on its fiber. -/
theorem sum_fiber {S : Type*} [CommSemiring S] (p : I ≃ J)
    (w : Fin n → Fin n → S) :
    (∑ σ : Fiber I J p, ∏ i : I, w i (σ.val i)) =
      ((n-I.card).factorial : S) * ∏ i : I, w i (p i) := by
  classical
  have hweight (σ : Fiber I J p) :
      (∏ i : I, w i (σ.val i)) = ∏ i : I, w i (p i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [σ.property i]
  simp_rw [hweight]
  simp [card_fiber, nsmul_eq_mul]

/-- Every permutation has a unique finite image and a unique restriction to it. -/
def imageRestriction (σ : Equiv.Perm (Fin n)) : I ≃ (I.image σ) where
  toFun i := ⟨σ i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩
  invFun j := ⟨σ.symm j, by
    rcases Finset.mem_image.mp j.property with ⟨i, hi, he⟩
    simpa [← he] using hi⟩
  left_inv i := by apply Subtype.ext; exact σ.symm_apply_apply i
  right_inv j := by apply Subtype.ext; exact σ.apply_symm_apply j

lemma image_eq_of_fiber (p : I ≃ J) (σ : Fiber I J p) : I.image σ.val = J := by
  ext j
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, he⟩
    have hp := σ.property ⟨i, hi⟩
    exact (he.symm.trans hp) ▸ (p ⟨i, hi⟩).property
  · intro hj
    let x := p.symm ⟨j, hj⟩
    exact Finset.mem_image.mpr ⟨x, x.property, by simpa [x] using σ.property x⟩

abbrev RestrictedData (I : Finset (Fin n)) := Σ J : Finset (Fin n), I ≃ J
abbrev CompletionData (I : Finset (Fin n)) :=
  Σ d : RestrictedData I, Fiber I d.1 d.2

/-- No multiplicity is lost by grouping first by the image subset, then the restriction. -/
def completionsEquiv : CompletionData I ≃ Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun d => d.2.val) (by
    constructor
    · rintro ⟨⟨J, p⟩, σ⟩ ⟨⟨J', p'⟩, σ'⟩ h
      have hJ : J = J' := (image_eq_of_fiber I J p σ).symm.trans
        ((congrArg (fun τ : Equiv.Perm (Fin n) => I.image τ) h).trans
          (image_eq_of_fiber I J' p' σ'))
      subst J'
      have hp : p = p' := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        exact (σ.property i).symm.trans ((congrArg (fun τ : Equiv.Perm (Fin n) => τ i) h).trans
          (σ'.property i))
      subst p'
      have hs : σ = σ' := Subtype.ext h
      subst σ'
      rfl
    · intro σ
      exact ⟨⟨⟨I.image σ, imageRestriction I σ⟩, ⟨σ, fun _ => rfl⟩⟩, rfl⟩)

/-- Exact regrouping of a full-permutation sum into restriction weights. -/
theorem sum_permutations {S : Type*} [CommSemiring S]
    (w : Fin n → Fin n → S) :
    (∑ σ : Equiv.Perm (Fin n), ∏ i : I, w i (σ i)) =
      ((n-I.card).factorial : S) *
        ∑ J : Finset (Fin n), ∑ p : I ≃ J, ∏ i : I, w i (p i) := by
  classical
  rw [← (completionsEquiv I).sum_comp (fun σ => ∏ i : I, w i (σ i))]
  simp only [Fintype.sum_sigma]
  change (∑ J : Finset (Fin n), ∑ p : I ≃ J,
    ∑ σ : Fiber I J p, ∏ i : I, w i (σ.val i)) = _
  simp_rw [sum_fiber]
  simp only [Finset.mul_sum]

end PermanentRestrictionFiber
#print axioms PermanentRestrictionFiber.card_fiber
#print axioms PermanentRestrictionFiber.sum_fiber

#print axioms PermanentRestrictionFiber.sum_permutations
