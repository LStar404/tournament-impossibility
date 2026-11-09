import Mathlib.Combinatorics.Enumerative.Composition
import OrderedResidualPolynomial
noncomputable section
namespace OrderedDegreeCompositionCount

/-- All positive-depth ordered degree assignments across all lengths, not a fixed-length box. -/
abbrev Degrees (D : ℕ) := Σb : ℕ,{d : Fin b → ℕ // (∀i,3 ≤ d i) ∧ (∑i,d i)=D}

def composition {D : ℕ} (p : Degrees D) : Composition D where
  blocks := List.ofFn p.2.val
  blocks_pos := by
    intro i hi
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
    have h := p.2.property.1 j
    omega
  blocks_sum := by simpa [List.sum_ofFn] using p.2.property.2

theorem composition_injective (D : ℕ) : Function.Injective (@composition D) := by
  rintro ⟨b,d⟩ ⟨c,e⟩ h
  have hl := congrArg (fun x : Composition D => x.blocks.length) h
  change (List.ofFn d.val).length=(List.ofFn e.val).length at hl
  simp only [List.length_ofFn] at hl
  subst c
  have hb := congrArg Composition.blocks h
  change List.ofFn d.val=List.ofFn e.val at hb
  have hd : d=e := Subtype.ext (List.ofFn_injective hb)
  subst e
  rfl

instance (D : ℕ) : Finite (Degrees D) := Finite.of_injective composition (composition_injective D)
instance (D : ℕ) : Fintype (Degrees D) := Fintype.ofFinite _

theorem degree_count (D : ℕ) : Fintype.card (Degrees D) ≤ 2^(D-1) := by
  calc
    _ ≤ Fintype.card (Composition D) := Fintype.card_le_of_injective _ (composition_injective D)
    _ = _ := composition_card D

/-- The actual Finsupp indexing admits no extra multiplicity beyond these degree lists. -/
def ofFinsupp {D b : ℕ} (d : Fin b →₀ ℕ) (hd : ∀i,3 ≤ d i) (hs : (∑i,d i)=D) : Degrees D :=
  ⟨b,⟨fun i => d i,hd,hs⟩⟩

theorem ofFinsupp_injective {D b : ℕ} (d e : Fin b →₀ ℕ)
    (hd : ∀i,3 ≤ d i) (he : ∀i,3 ≤ e i) (hs : (∑i,d i)=D) (ht : (∑i,e i)=D)
    (h : ofFinsupp d hd hs=ofFinsupp e he ht) : d=e := by
  have hh := congrArg composition h
  have hl := congrArg Composition.blocks hh
  have hv := List.ofFn_injective hl
  exact Finsupp.ext (fun i => congrFun hv i)
end OrderedDegreeCompositionCount
#print axioms OrderedDegreeCompositionCount.degree_count
