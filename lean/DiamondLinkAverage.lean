import DiamondFreeRepresentation
noncomputable section
namespace DiamondLinkAverage
open Finset DiamondGap
variable {V : Type*} [Fintype V] [DecidableEq V]

def link (T : Tournament V) (p : V) : Finset (Finset V) :=
  T.diamonds.filter (fun s => p ∈ s)

lemma mem_link (T : Tournament V) (p : V) (s : Finset V) :
    s ∈ link T p ↔ T.IsDiamond s ∧ p ∈ s := by
  simp [link, T.mem_diamonds]

/-- Each actual unordered diamond contributes to exactly four pivot links. -/
theorem total_link_card (T : Tournament V) :
    (∑ p : V, (link T p).card) = 4*T.diamonds.card := by
  classical
  have hcard (p : V) : (link T p).card =
      ∑ s ∈ T.diamonds, if p ∈ s then (1 : ℕ) else 0 := by simp [link]
  simp_rw [hcard]
  rw [sum_comm]
  have he : (∑ s ∈ T.diamonds, ∑ p : V, if p ∈ s then (1 : ℕ) else 0) =
      ∑ s ∈ T.diamonds, s.card := by
    apply sum_congr rfl; intro s hs
    simp
  rw [he]
  calc
    _ = ∑ _s ∈ T.diamonds, 4 := by
      apply sum_congr rfl; intro s hs
      exact ((T.mem_diamonds s).mp hs).1
    _ = _ := by simp [Nat.mul_comm]

/-- A real pivot with at most average diamond incidence, without division. -/
theorem exists_small_link [Nonempty V] (T : Tournament V) :
    ∃ p : V, Fintype.card V * (link T p).card ≤ 4*T.diamonds.card := by
  classical
  by_contra h
  have hlt : ∀ p : V, 4*T.diamonds.card < Fintype.card V * (link T p).card := by
    intro p
    have hp : ¬ Fintype.card V * (link T p).card ≤ 4*T.diamonds.card := by
      intro hp; exact h ⟨p,hp⟩
    omega
  let p₀ : V := Classical.choice inferInstance
  have hs : (∑ _p : V, 4*T.diamonds.card) <
      ∑ p : V, Fintype.card V * (link T p).card := by
    apply sum_lt_sum
    · intro p hp; exact (hlt p).le
    · exact ⟨p₀, mem_univ p₀, hlt p₀⟩
  simp only [sum_const, card_univ, smul_eq_mul, nsmul_eq_mul, ← mul_sum,
    total_link_card T] at hs
  omega
end DiamondLinkAverage
#print axioms DiamondLinkAverage.total_link_card
#print axioms DiamondLinkAverage.exists_small_link
