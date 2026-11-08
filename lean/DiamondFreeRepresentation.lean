import DiamondGap
import ColorGraphRepair
import TournamentColorEnumeration
namespace DiamondFreeRepresentation
open DiamondGap

variable {V : Type*} [DecidableEq V]

/-- Ordinary diamond absence, using the existing four-vertex tournament definition. -/
def DiamondFree (T : Tournament V) : Prop := ∀ s, ¬T.IsDiamond s

/-- Explicit diagonal sign switching. It is not asserted to be an ordinary isomorphism. -/
def switched (T : Tournament V) (d : V → ℤ) (hd : ∀ x, (d x)^2=1) : Tournament V where
  S a b := d a * T.S a b * d b
  skew a b := by rw [T.skew a b]; ring
  unit a b hab := by
    rcases sq_eq_one_iff.mp (hd a) with ha | ha <;>
      rcases sq_eq_one_iff.mp (hd b) with hb | hb <;>
      rcases T.unit a b hab with ht | ht <;> simp [ha, hb, ht]

omit [DecidableEq V] in
/-- Pfaffian changes by the product of the four switching signs. -/
theorem switched_quad (T : Tournament V) (d : V → ℤ) (hd : ∀ x, (d x)^2=1)
    (a b c e : V) :
    (switched T d hd).quad a b c e = d a*d b*d c*d e*T.quad a b c e := by
  simp only [Tournament.quad, pf, switched]
  ring

omit [DecidableEq V] in
/-- Crucial invariant: squared four-vertex Pfaffian is genuinely switching invariant. -/
theorem switched_quad_sq (T : Tournament V) (d : V → ℤ) (hd : ∀ x, (d x)^2=1)
    (a b c e : V) :
    (switched T d hd).quad a b c e ^ 2 = T.quad a b c e ^ 2 := by
  rw [switched_quad]
  simp only [mul_pow, hd, one_mul]

theorem no_quad_nine (T : Tournament V) (hT : DiamondFree T) (a b c d : V) :
    T.quad a b c d ^ 2 ≠ 9 := by
  intro h
  exact hT _ (T.diamond_of_quad a b c d h)

/-- Switching preserves ordinary diamond absence, via the verified local criterion. -/
theorem switched_diamondFree (T : Tournament V) (d : V → ℤ) (hd : ∀ x, (d x)^2=1)
    (hT : DiamondFree T) : DiamondFree (switched T d hd) := by
  intro s hs
  obtain ⟨_,a,b,c,e,_,hq⟩ := hs
  rw [switched_quad_sq] at hq
  exact no_quad_nine T hT a b c e hq

/-- Switch signs chosen from a root's actual outgoing row. -/
def pivotSign (T : Tournament V) (p x : V) : ℤ := if x=p then 1 else T.S p x

theorem pivotSign_sq (T : Tournament V) (p x : V) : (pivotSign T p x)^2=1 := by
  unfold pivotSign
  split_ifs with h
  · norm_num
  · rcases T.unit p x (Ne.symm h) with ht | ht <;> simp [ht]

/-- The chosen pivot is an actual source after the explicitly specified switch. -/
theorem pivot_source (T : Tournament V) (p x : V) (hx : x ≠ p) :
    (switched T (pivotSign T p) (pivotSign_sq T p)).S p x = 1 := by
  have ht := pivotSign_sq T p x
  simp only [pivotSign, ite_eq_right hx] at ht
  simpa [switched, pivotSign, hx, pow_two] using ht

/-- A source in a diamond-free tournament forces the remaining relation to be
transitive: a cyclic triangle with that source would be an ordinary diamond. -/
theorem source_transitive (U : Tournament V) (p : V)
    (hs : ∀ x, x ≠ p → U.S p x = 1) (hU : DiamondFree U) :
    ∀ a b c, U.S a b = 1 → U.S b c = 1 → U.S a c = 1 := by
  intro a b c hab hbc
  have habne : a ≠ b := by intro he; subst b; rw [U.diagonal] at hab; norm_num at hab
  have hbcne : b ≠ c := by intro he; subst c; rw [U.diagonal] at hbc; norm_num at hbc
  have hacne : a ≠ c := by
    intro he; subst c
    have ht := U.skew a b
    rw [hab, hbc] at ht
    norm_num at ht
  have hbp : b ≠ p := by
    intro he; subst b
    have ht := hs a habne
    have hk := U.skew a p
    rw [hab, ht] at hk
    norm_num at hk
  have hcp : c ≠ p := by
    intro he; subst c
    have ht := hs b hbp
    have hk := U.skew b p
    rw [hbc, ht] at hk
    norm_num at hk
  by_cases hap : a = p
  · subst a
    exact hs c hcp
  · rcases U.unit a c hacne with ht | ht
    · exact ht
    · exfalso
      apply no_quad_nine U hU p a b c
      simp only [Tournament.quad, pf]
      rw [hs a hap, hs b hbp, hs c hcp, hab, hbc, ht]
      norm_num

/-- Every diamond-free tournament has an explicitly realizable transitive
sign-switch. This theorem does not call that switch an ordinary isomorphism. -/
theorem exists_transitive_switch (T : Tournament V) (hT : DiamondFree T) :
    ∃ (d : V → ℤ) (U : Tournament V),
      (∀ x, (d x)^2=1) ∧
      (∀ a b, U.S a b = d a * T.S a b * d b) ∧
      (∀ a b c, U.S a b = 1 → U.S b c = 1 → U.S a c = 1) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hv =>
    refine ⟨fun _ => 1, T, by simp, by simp, ?_⟩
    intro a
    exact (hv.false a).elim
  | inr hv =>
    let p : V := Classical.choice hv
    refine ⟨pivotSign T p, switched T (pivotSign T p) (pivotSign_sq T p),
      pivotSign_sq T p, fun _ _ => rfl, ?_⟩
    exact source_transitive _ p (pivot_source T p)
      (switched_diamondFree T _ _ hT)

/-- Empty counted diamond set gives the ordinary diamond-free hypothesis. -/
theorem diamondFree_of_card_zero [Fintype V] (T : Tournament V)
    (h : T.diamonds.card = 0) : DiamondFree T := by
  classical
  have he : T.diamonds = ∅ := Finset.card_eq_zero.mp h
  intro s hs
  have hm := (T.mem_diamonds s).mpr hs
  rw [he] at hm
  exact Finset.notMem_empty s hm

/-- Every finite ordinary diamond-free tournament is, under an actual vertex
enumeration, a color-word graph. The proof uses a sign switch internally but
reconstructs the ORIGINAL matrix; no switching-is-isomorphism premise is used. -/
theorem diamondFree_color_representation [Fintype V] (T : Tournament V)
    (hT : DiamondFree T) :
    ∃ (w : List Bool) (e : Fin (Fintype.card V) ≃ V),
      w.length = Fintype.card V ∧
      ∀ i j, (T.S (e i) (e j) : ℝ) = ColorTransport.colorGraph w i j := by
  obtain ⟨d, U, hd, hs, ht⟩ := exists_transitive_switch T hT
  exact ColorTransport.representation_of_transitive_switch T U d hd hs ht

/-- The endpoint stated directly in terms of the existing unordered diamond count. -/
theorem zero_diamonds_color_representation [Fintype V] (T : Tournament V)
    (hT : T.diamonds.card = 0) :
    ∃ (w : List Bool) (e : Fin (Fintype.card V) ≃ V),
      w.length = Fintype.card V ∧
      ∀ i j, (T.S (e i) (e j) : ℝ) = ColorTransport.colorGraph w i j :=
  diamondFree_color_representation T (diamondFree_of_card_zero T hT)

#print axioms diamondFree_color_representation
#print axioms zero_diamonds_color_representation
#print axioms switched_quad_sq
#print axioms switched_diamondFree
#print axioms source_transitive
#print axioms exists_transitive_switch
#print axioms diamondFree_of_card_zero
end DiamondFreeRepresentation
