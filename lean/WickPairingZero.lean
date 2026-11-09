import BipartitePairingPermanent
import Mathlib

noncomputable section
open scoped BigOperators
namespace WickPairingZero

abbrev Vertex (n : ℕ) := Fin n ⊕ Fin n
abbrev Pairing (n : ℕ) := {p : Equiv.Perm (Vertex n) //
  (∀ x, p (p x) = x) ∧ (∀ x, p x ≠ x)}

def key {n : ℕ} : Vertex n → ℕ
  | Sum.inl i => i.val
  | Sum.inr i => n+i.val

def color {n : ℕ} : Vertex n → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

theorem key_injective {n : ℕ} : Function.Injective (@key n) := by
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

def representatives {n : ℕ} (p : Pairing n) : Finset (Vertex n) :=
  Finset.univ.filter (fun x => key x < key (p.val x))

def weight {n : ℕ} {R : Type*} [CommSemiring R]
    (C : Matrix (Vertex n) (Vertex n) R) (p : Pairing n) : R :=
  ∏ x ∈ representatives p, C x (p.val x)

def Bipartite {n : ℕ} (p : Pairing n) : Prop :=
  ∀ x, color x ≠ color (p.val x)

instance {n : ℕ} (p : Pairing n) : Decidable (Bipartite p) := Classical.propDecidable _

/-- An actual same-colour edge contributes a zero factor, whichever endpoint
is chosen as its unique representative. -/
theorem weight_eq_zero_of_same_color {n : ℕ} {R : Type*} [CommSemiring R]
    (C : Matrix (Vertex n) (Vertex n) R) (p : Pairing n)
    (hzero : ∀ x y, color x = color y → C x y = 0)
    (x : Vertex n) (hx : color x = color (p.val x)) : weight C p = 0 := by
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

theorem nonbipartite_weight_eq_zero {n : ℕ} {R : Type*} [CommSemiring R]
    (C : Matrix (Vertex n) (Vertex n) R) (p : Pairing n)
    (hzero : ∀ x y, color x = color y → C x y = 0)
    (hp : ¬ Bipartite p) : weight C p = 0 := by
  classical
  simp only [Bipartite, not_forall, not_not] at hp
  obtain ⟨x,hx⟩ := hp
  exact weight_eq_zero_of_same_color C p hzero x hx

/-- The sum is over all perfect pairings, not only bipartite pairings. -/
theorem sum_eq_bipartite_filter {n : ℕ} {R : Type*} [CommSemiring R]
    (C : Matrix (Vertex n) (Vertex n) R)
    (hzero : ∀ x y, color x = color y → C x y = 0) :
    ∑ p : Pairing n, weight C p =
      ∑ p ∈ Finset.univ.filter Bipartite, weight C p := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  apply nonbipartite_weight_eq_zero C p hzero
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot

end WickPairingZero
#print axioms WickPairingZero.nonbipartite_weight_eq_zero
#print axioms WickPairingZero.sum_eq_bipartite_filter
