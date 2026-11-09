import RepeatedLabelPairing

noncomputable section
open scoped BigOperators
namespace FullFourthMoment
abbrev V := Fin 2 ⊕ Fin 2
abbrev P := WickPairingZero.Pairing 2

def p0 : P := ⟨Equiv.swap (Sum.inl 0 : V) (Sum.inl 1) *
  Equiv.swap (Sum.inr 0) (Sum.inr 1), by decide⟩
def p1 : P := ⟨Equiv.swap (Sum.inl 0 : V) (Sum.inr 0) *
  Equiv.swap (Sum.inl 1) (Sum.inr 1), by decide⟩
def p2 : P := ⟨Equiv.swap (Sum.inl 0 : V) (Sum.inr 1) *
  Equiv.swap (Sum.inl 1) (Sum.inr 0), by decide⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem all_pairings : (Finset.univ : Finset P) = {p0,p1,p2} := by decide

/-- Full fourth moment with no zero-diagonal assumption, obtained by
exhausting the three genuine pairings of four distinct occurrence positions. -/
theorem fourth {L S : Type*} [CommSemiring S]
    (C : L → L → S) (a : V → L) :
    RepeatedLabelPairing.moment C a =
      C (a (Sum.inl 0)) (a (Sum.inl 1)) * C (a (Sum.inr 0)) (a (Sum.inr 1)) +
      C (a (Sum.inl 0)) (a (Sum.inr 0)) * C (a (Sum.inl 1)) (a (Sum.inr 1)) +
      C (a (Sum.inl 0)) (a (Sum.inr 1)) * C (a (Sum.inl 1)) (a (Sum.inr 0)) := by
  unfold RepeatedLabelPairing.moment
  rw [all_pairings]
  have h01 : p0 ≠ p1 := by decide
  have h02 : p0 ≠ p2 := by decide
  have h12 : p1 ≠ p2 := by decide
  rw [Finset.sum_insert (show p0 ∉ ({p1,p2} : Finset P) by simp [h01,h02]),
    Finset.sum_insert (show p1 ∉ ({p2} : Finset P) by simp [h12]), Finset.sum_singleton]
  have hr0 : WickPairingZero.representatives p0 = {Sum.inl 0,Sum.inr 0} := by decide
  have hr1 : WickPairingZero.representatives p1 = {Sum.inl 0,Sum.inl 1} := by decide
  have hr2 : WickPairingZero.representatives p2 = {Sum.inl 0,Sum.inl 1} := by decide
  unfold WickPairingZero.weight
  rw [hr0,hr1,hr2]
  norm_num [p0,p1,p2, Equiv.swap_apply_def]
  <;> ring

/-- Repeated-coordinate full fourth moment, including nonzero diagonal. -/
theorem repeated_xxyy {L S : Type*} [CommSemiring S]
    (C : L → L → S) (x y : L) :
    RepeatedLabelPairing.moment C (Sum.elim (fun _ : Fin 2 => x) (fun _ : Fin 2 => y)) =
      C x x * C y y + 2 * C x y ^ 2 := by
  rw [fourth]
  simp only [Sum.elim_inl,Sum.elim_inr]
  ring


end FullFourthMoment
#print axioms FullFourthMoment.fourth

#print axioms FullFourthMoment.repeated_xxyy
