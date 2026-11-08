import DiamondGap
import ColorGraphRepair

namespace ColorTransport

/-- A finite transitive tournament admits an actual ordered enumeration.
Transitivity is an explicit premise, not asserted for arbitrary tournaments. -/
theorem transitive_tournament_enumeration {V : Type*} [Fintype V] [DecidableEq V]
    (U : DiamondGap.Tournament V)
    (htrans : ∀ a b c, U.S a b = 1 → U.S b c = 1 → U.S a c = 1) :
    ∃ e : Fin (Fintype.card V) ≃ V,
      ∀ i j, (U.S (e i) (e j) : ℝ) = orderSign i j := by
  classical
  let r : V → V → Prop := fun a b => U.S a b = 1
  let : IsStrictTotalOrder V r := {
    irrefl := by intro a; change U.S a a ≠ 1; rw [U.diagonal a]; norm_num
    trans := by intro a b c hab hbc; exact htrans a b c hab hbc
    trichotomous := by
      intro a b hab hba
      by_contra hne
      have h := U.unit a b hne
      have hs := U.skew a b
      change U.S a b ≠ 1 at hab
      change U.S b a ≠ 1 at hba
      omega }
  let : LinearOrder V := linearOrderOfSTO r
  let f : Fin (Fintype.card V) ≃o V := Fintype.orderIsoFinOfCardEq V rfl
  refine ⟨f.toEquiv, ?_⟩
  intro i j
  simp only [OrderIso.coe_toEquiv]
  by_cases hij : i < j
  · have h : U.S (f i) (f j) = 1 := (f.lt_iff_lt).mpr hij
    rw [h]
    simp [orderSign, Fin.lt_def.mp hij]
  · by_cases hji : j < i
    · have h : U.S (f j) (f i) = 1 := (f.lt_iff_lt).mpr hji
      rw [U.skew, h]
      simp [orderSign, show ¬(i.val < j.val) from hij, Fin.lt_def.mp hji]
    · have he : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      rw [U.diagonal]
      simp [orderSign]

/-- A transitive switched tournament yields a concrete color word representation
of the original tournament. The final e is only an ordinary vertex enumeration;
the signs are retained in the word and are not treated as an isomorphism. -/
theorem representation_of_transitive_switch {V : Type*} [Fintype V] [DecidableEq V]
    (T U : DiamondGap.Tournament V) (d : V → ℤ)
    (hd : ∀ x, (d x)^2 = 1)
    (hswitch : ∀ a b, U.S a b = d a * T.S a b * d b)
    (htrans : ∀ a b c, U.S a b = 1 → U.S b c = 1 → U.S a c = 1) :
    ∃ (w : List Bool) (e : Fin (Fintype.card V) ≃ V),
      w.length = Fintype.card V ∧
      ∀ i j, (T.S (e i) (e j) : ℝ) = colorGraph w i j := by
  classical
  obtain ⟨e, he⟩ := transitive_tournament_enumeration U htrans
  let b : Fin (Fintype.card V) → Bool := fun i => decide (d (e i) = 1)
  let w := List.ofFn b
  have hb (i : Fin (Fintype.card V)) : color (b i) = d (e i) := by
    have hx : d (e i) = 1 ∨ d (e i) = -1 := (sq_eq_one_iff).mp (hd (e i))
    rcases hx with hx | hx <;> simp [b, color, hx]
  have hc (i : Fin (Fintype.card V)) : colorR w i = (d (e i) : ℝ) := by
    have hg : w.getD i false = b i := by
      simp [w, List.getD_eq_getElem?_getD, i.isLt]
    simp only [colorR, hg, hb]
  have hinv (a c : V) : T.S a c = d a * U.S a c * d c := by
    symm
    calc
      d a * U.S a c * d c = (d a)^2 * T.S a c * (d c)^2 := by rw [hswitch]; ring
      _ = T.S a c := by rw [hd, hd]; ring
  refine ⟨w, e, by simp [w], ?_⟩
  intro i j
  rw [hinv]
  push_cast
  rw [he i j]
  unfold colorGraph
  rw [hc i, hc j]
  ring

#print axioms transitive_tournament_enumeration
#print axioms representation_of_transitive_switch
end ColorTransport
