import WickPairingPermanent

noncomputable section
open scoped BigOperators
namespace RepeatedLabelPairing

/-- Labels need not be injective: pairing positions remain distinct even
when two occurrences carry the same coordinate label. -/
def moment {n : ℕ} {L S : Type*} [CommSemiring S]
    (C : L → L → S) (a : Fin n ⊕ Fin n → L) : S :=
  ∑ p : WickPairingZero.Pairing n, WickPairingZero.weight (fun i j => C (a i) (a j)) p

def cross {n : ℕ} {L S : Type*} (C : L → L → S)
    (a : Fin n ⊕ Fin n → L) : Matrix (Fin n) (Fin n) S :=
  fun i j => C (a (Sum.inl i)) (a (Sum.inr j))

theorem moment_eq_permanent {n : ℕ} {L S : Type*} [CommSemiring S]
    (C : L → L → S) (a : Fin n ⊕ Fin n → L)
    (hs : ∀ x y, C x y = C y x)
    (hl : ∀ i j, C (a (Sum.inl i)) (a (Sum.inl j)) = 0)
    (hr : ∀ i j, C (a (Sum.inr i)) (a (Sum.inr j)) = 0) :
    moment C a = Matrix.permanent (cross C a) := by
  have hC : (fun i j => C (a i) (a j)) = WickPairingPermanent.covariance (cross C a) := by
    funext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hl i j
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => exact hs _ _
      | inr j => exact hr i j
  unfold moment
  rw [hC]
  exact WickPairingPermanent.all_pairings_eq_permanent _

/-- Genuine position-reordering invariance in the zero-monochromatic block
case. This does not assert arbitrary full Wick reordering invariance. -/
theorem color_permutation_invariant {n : ℕ} {L S : Type*} [CommSemiring S]
    (C : L → L → S) (a : Fin n ⊕ Fin n → L)
    (hs : ∀ x y, C x y = C y x)
    (hl : ∀ i j, C (a (Sum.inl i)) (a (Sum.inl j)) = 0)
    (hr : ∀ i j, C (a (Sum.inr i)) (a (Sum.inr j)) = 0)
    (σ τ : Equiv.Perm (Fin n)) :
    moment C (a ∘ (σ.sumCongr τ)) = moment C a := by
  rw [moment_eq_permanent C a hs hl hr]
  rw [moment_eq_permanent C _ hs (fun i j => hl (σ i) (σ j)) (fun i j => hr (τ i) (τ j))]
  change Matrix.permanent ((cross C a).submatrix σ τ) = _
  have he : (cross C a).submatrix σ τ = ((cross C a).submatrix σ id).submatrix id τ := rfl
  rw [he, Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]

/-- Four positions, only two coordinate labels. All full pairings are
summed before zero same-coordinate factors are eliminated. -/
theorem repeated_four {L S : Type*} [CommSemiring S]
    (C : L → L → S) (x y : L) (hs : ∀ u v, C u v = C v u)
    (hxx : C x x = 0) (hyy : C y y = 0) :
    moment C (Sum.elim (fun _ : Fin 2 => x) (fun _ : Fin 2 => y)) =
      2 * (C x y)^2 := by
  rw [moment_eq_permanent C _ hs (fun _ _ => hxx) (fun _ _ => hyy)]
  simp [Matrix.permanent, cross, Fintype.card_perm, Fintype.card_fin]

/-- Agreement with the previously checked positional squarefree pairing
sum. The new label map need not be injective, unlike a squarefree monomial. -/
theorem identity_labels {n : ℕ} {S : Type*} [CommSemiring S]
    (A : Matrix (Fin n) (Fin n) S) :
    moment (WickPairingPermanent.covariance A) id = Matrix.permanent A := by
  exact WickPairingPermanent.all_pairings_eq_permanent A

end RepeatedLabelPairing
#print axioms RepeatedLabelPairing.repeated_four
#print axioms RepeatedLabelPairing.color_permutation_invariant
