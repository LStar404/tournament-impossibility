import RectangularPairing

noncomputable section
open scoped BigOperators
namespace FinitePairingTransport

abbrev Pairing (V : Type*) := {p : Equiv.Perm V //
  (∀ x, p (p x) = x) ∧ (∀ x, p x ≠ x)}

instance {V : Type*} [Fintype V] : Fintype (Pairing V) := by
  classical
  exact Fintype.ofFinite _

def transport {V W : Type*} (e : V ≃ W) (p : Pairing V) : Pairing W :=
  ⟨e.permCongr p.val, by
    constructor
    · intro x
      change e (p.val (e.symm (e (p.val (e.symm x))))) = x
      simp only [Equiv.symm_apply_apply, p.property.1, Equiv.apply_symm_apply]
    · intro x h
      apply p.property.2 (e.symm x)
      apply e.injective
      simpa using h⟩

def transportEquiv {V W : Type*} (e : V ≃ W) : Pairing V ≃ Pairing W where
  toFun := transport e
  invFun := transport e.symm
  left_inv p := by
    apply Subtype.ext
    ext x
    simp [transport, Equiv.permCongr_def]
  right_inv p := by
    apply Subtype.ext
    ext x
    simp [transport, Equiv.permCongr_def]

/-- The key orders each colour by its finite enumeration, with left first. -/
def key {L R : Type*} {a b : ℕ} (eL : L ≃ Fin a) (eR : R ≃ Fin b)
    (x : L ⊕ R) : ℕ := RectangularPairing.key ((eL.sumCongr eR) x)

def representatives {L R : Type*} [Fintype L] [Fintype R]
    {a b : ℕ} (eL : L ≃ Fin a) (eR : R ≃ Fin b) (p : Pairing (L ⊕ R)) :
    Finset (L ⊕ R) := by
  classical
  exact Finset.univ.filter (fun x => key eL eR x < key eL eR (p.val x))

def weight {L R S : Type*} [Fintype L] [Fintype R] [CommSemiring S]
    {a b : ℕ} (eL : L ≃ Fin a) (eR : R ≃ Fin b)
    (C : Matrix (L ⊕ R) (L ⊕ R) S) (p : Pairing (L ⊕ R)) : S :=
  ∏ x ∈ representatives eL eR p, C x (p.val x)

def transportedMatrix {L R S : Type*} {a b : ℕ}
    (eL : L ≃ Fin a) (eR : R ≃ Fin b)
    (C : Matrix (L ⊕ R) (L ⊕ R) S) :
    Matrix (RectangularPairing.Vertex a b) (RectangularPairing.Vertex a b) S :=
  fun x y => C ((eL.sumCongr eR).symm x) ((eL.sumCongr eR).symm y)

theorem weight_transport {L R S : Type*} [Fintype L] [Fintype R] [CommSemiring S]
    {a b : ℕ} (eL : L ≃ Fin a) (eR : R ≃ Fin b)
    (C : Matrix (L ⊕ R) (L ⊕ R) S) (p : Pairing (L ⊕ R)) :
    weight eL eR C p = RectangularPairing.weight (transportedMatrix eL eR C)
      (transport (eL.sumCongr eR) p) := by
  classical
  unfold weight RectangularPairing.weight
  apply Finset.prod_equiv (eL.sumCongr eR)
  · intro x
    simp [representatives, RectangularPairing.representatives, key,
      transport, Equiv.permCongr_def]
  · intro x hx
    simp [transportedMatrix, transport, Equiv.permCongr_def]

theorem sum_transport {L R S : Type*} [Fintype L] [Fintype R] [CommSemiring S]
    {a b : ℕ} (eL : L ≃ Fin a) (eR : R ≃ Fin b)
    (C : Matrix (L ⊕ R) (L ⊕ R) S) :
    ∑ p : Pairing (L ⊕ R), weight eL eR C p =
      ∑ p : RectangularPairing.Pairing a b,
        RectangularPairing.weight (transportedMatrix eL eR C) p := by
  classical
  exact Fintype.sum_equiv (transportEquiv (eL.sumCongr eR)) _ _
    (fun p => weight_transport eL eR C p)

end FinitePairingTransport
#print axioms FinitePairingTransport.sum_transport
