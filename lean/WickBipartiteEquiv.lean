import WickPairingZero

noncomputable section
open scoped BigOperators
namespace WickBipartiteEquiv
open WickPairingZero
abbrev BP (n : ℕ) := {p : Pairing n // Bipartite p}

theorem left_exists {n : ℕ} (p : BP n) (i : Fin n) :
    ∃ j, p.val.val (Sum.inl i) = Sum.inr j := by
  have h := p.property (Sum.inl i)
  cases he : p.val.val (Sum.inl i) with
  | inl j => simp [he, color] at h
  | inr j => exact ⟨j,rfl⟩

theorem right_exists {n : ℕ} (p : BP n) (j : Fin n) :
    ∃ i, p.val.val (Sum.inr j) = Sum.inl i := by
  have h := p.property (Sum.inr j)
  cases he : p.val.val (Sum.inr j) with
  | inl i => exact ⟨i,rfl⟩
  | inr i => simp [he, color] at h

def left {n : ℕ} (p : BP n) (i : Fin n) : Fin n := (left_exists p i).choose
def right {n : ℕ} (p : BP n) (i : Fin n) : Fin n := (right_exists p i).choose

theorem left_spec {n : ℕ} (p : BP n) (i : Fin n) :
    p.val.val (Sum.inl i) = Sum.inr (left p i) := (left_exists p i).choose_spec
 theorem right_spec {n : ℕ} (p : BP n) (i : Fin n) :
    p.val.val (Sum.inr i) = Sum.inl (right p i) := (right_exists p i).choose_spec

def toPairing {n : ℕ} (p : BP n) : BipartitePairingPermanent.Pairing n where
  left := left p
  right := right p
  right_left i := by
    have h := p.val.property.1 (Sum.inl i)
    rw [left_spec, right_spec] at h
    exact Sum.inl.inj h
  left_right i := by
    have h := p.val.property.1 (Sum.inr i)
    rw [right_spec, left_spec] at h
    exact Sum.inr.inj h

def fromPairing {n : ℕ} (p : BipartitePairingPermanent.Pairing n) : BP n :=
  ⟨⟨{toFun := BipartitePairingPermanent.partner p,
      invFun := BipartitePairingPermanent.partner p,
      left_inv := BipartitePairingPermanent.partner_involutive p,
      right_inv := BipartitePairingPermanent.partner_involutive p},
    BipartitePairingPermanent.partner_involutive p,
    BipartitePairingPermanent.partner_ne_self p⟩,
    by
      intro x
      change color x ≠ color (BipartitePairingPermanent.partner p x)
      cases x <;> simp [BipartitePairingPermanent.partner,color]⟩

def pairingEquiv (n : ℕ) : BP n ≃ BipartitePairingPermanent.Pairing n where
  toFun := toPairing
  invFun := fromPairing
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    cases x with
    | inl i => exact (left_spec p i).symm
    | inr i => exact (right_spec p i).symm
  right_inv p := by
    apply BipartitePairingPermanent.Pairing.ext
    · funext i
      exact Sum.inr.inj (left_spec (fromPairing p) i).symm
    · funext i
      exact Sum.inl.inj (right_spec (fromPairing p) i).symm

end WickBipartiteEquiv
#print axioms WickBipartiteEquiv.pairingEquiv
