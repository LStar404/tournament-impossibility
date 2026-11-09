import WickPairingPermanent

noncomputable section
open scoped BigOperators
namespace RectangularPairing

abbrev Vertex (a b : ℕ) := Fin a ⊕ Fin b
abbrev Pairing (a b : ℕ) := {p : Equiv.Perm (Vertex a b) //
  (∀ x, p (p x) = x) ∧ (∀ x, p x ≠ x)}

def key {a b : ℕ} : Vertex a b → ℕ
  | Sum.inl i => i.val
  | Sum.inr j => a+j.val

def color {a b : ℕ} : Vertex a b → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

def Bipartite {a b : ℕ} (p : Pairing a b) : Prop :=
  ∀ x, color x ≠ color (p.val x)

instance {a b : ℕ} (p : Pairing a b) : Decidable (Bipartite p) := Classical.propDecidable _

def representatives {a b : ℕ} (p : Pairing a b) : Finset (Vertex a b) :=
  Finset.univ.filter (fun x => key x < key (p.val x))

def weight {a b : ℕ} {R : Type*} [CommSemiring R]
    (C : Matrix (Vertex a b) (Vertex a b) R) (p : Pairing a b) : R :=
  ∏ x ∈ representatives p, C x (p.val x)

theorem key_injective {a b : ℕ} : Function.Injective (@key a b) := by
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => simp only [key] at h; exact congrArg Sum.inl (Fin.ext h)
    | inr j => simp only [key] at h; have := i.isLt; omega
  | inr i =>
    cases y with
    | inl j => simp only [key] at h; have := j.isLt; omega
    | inr j => simp only [key] at h; exact congrArg Sum.inr (Fin.ext (by omega))

theorem exactly_one_representative {a b : ℕ} (p : Pairing a b) (x : Vertex a b) :
    x ∈ representatives p ↔ p.val x ∉ representatives p := by
  have hne : key x ≠ key (p.val x) := by
    intro h
    exact p.property.2 x (key_injective h).symm
  simp only [representatives, Finset.mem_filter, Finset.mem_univ, true_and, p.property.1 x]
  omega

abbrev BP (a b : ℕ) := {p : Pairing a b // Bipartite p}

theorem left_exists {a b : ℕ} (p : BP a b) (i : Fin a) :
    ∃ j, p.val.val (Sum.inl i) = Sum.inr j := by
  have h := p.property (Sum.inl i)
  cases he : p.val.val (Sum.inl i) with
  | inl j => simp [he, color] at h
  | inr j => exact ⟨j,rfl⟩

theorem right_exists {a b : ℕ} (p : BP a b) (j : Fin b) :
    ∃ i, p.val.val (Sum.inr j) = Sum.inl i := by
  have h := p.property (Sum.inr j)
  cases he : p.val.val (Sum.inr j) with
  | inl i => exact ⟨i,rfl⟩
  | inr i => simp [he, color] at h

def left {a b : ℕ} (p : BP a b) (i : Fin a) : Fin b := (left_exists p i).choose
def right {a b : ℕ} (p : BP a b) (i : Fin b) : Fin a := (right_exists p i).choose

theorem left_spec {a b : ℕ} (p : BP a b) (i : Fin a) :
    p.val.val (Sum.inl i) = Sum.inr (left p i) := (left_exists p i).choose_spec
theorem right_spec {a b : ℕ} (p : BP a b) (i : Fin b) :
    p.val.val (Sum.inr i) = Sum.inl (right p i) := (right_exists p i).choose_spec

def partnerEquiv {a b : ℕ} (p : BP a b) : Fin a ≃ Fin b where
  toFun := left p
  invFun := right p
  left_inv i := by
    have h := p.val.property.1 (Sum.inl i)
    rw [left_spec, right_spec] at h
    exact Sum.inl.inj h
  right_inv i := by
    have h := p.val.property.1 (Sum.inr i)
    rw [right_spec, left_spec] at h
    exact Sum.inr.inj h

theorem sizes_equal {a b : ℕ} (p : BP a b) : a = b := by
  simpa using Fintype.card_congr (partnerEquiv p)

theorem nonbipartite_weight_eq_zero {a b : ℕ} {R : Type*} [CommSemiring R]
    (C : Matrix (Vertex a b) (Vertex a b) R) (p : Pairing a b)
    (hzero : ∀ x y, color x = color y → C x y = 0)
    (hp : ¬ Bipartite p) : weight C p = 0 := by
  classical
  simp only [Bipartite, not_forall, not_not] at hp
  obtain ⟨x,hx⟩ := hp
  have hne : key x ≠ key (p.val x) := by
    intro h
    exact p.property.2 x (key_injective h).symm
  unfold weight
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply Finset.prod_eq_zero (i := x)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
    · exact hzero x (p.val x) hx
  · apply Finset.prod_eq_zero (i := p.val x)
    · simp only [representatives, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [p.property.1 x] using hgt
    · apply hzero
      simpa only [p.property.1 x] using hx.symm

theorem unequal_sum_zero {a b : ℕ} {R : Type*} [CommSemiring R]
    (C : Matrix (Vertex a b) (Vertex a b) R)
    (hzero : ∀ x y, color x = color y → C x y = 0) (hab : a ≠ b) :
    ∑ p : Pairing a b, weight C p = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  apply nonbipartite_weight_eq_zero C p hzero
  intro h
  exact hab (sizes_equal ⟨p,h⟩)

end RectangularPairing
#print axioms RectangularPairing.unequal_sum_zero
