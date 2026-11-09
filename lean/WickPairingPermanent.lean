import WickBipartiteEquiv

noncomputable section
open scoped BigOperators
namespace WickPairingPermanent
open WickPairingZero WickBipartiteEquiv

theorem exactly_one_representative {n : ℕ} (p : Pairing n) (x : Vertex n) :
    x ∈ representatives p ↔ p.val x ∉ representatives p := by
  have hne : key x ≠ key (p.val x) := by
    intro h
    exact p.property.2 x (key_injective h).symm
  simp only [representatives, Finset.mem_filter, Finset.mem_univ, true_and, p.property.1 x]
  omega

theorem weight_eq_left_product {n : ℕ} {R : Type*} [CommSemiring R]
    (C : Matrix (Vertex n) (Vertex n) R) (p : BP n) :
    weight C p.val = ∏ i, C (Sum.inl i) (Sum.inr (left p i)) := by
  classical
  symm
  unfold weight
  apply Finset.prod_bij (fun i _ => Sum.inl i)
  · intro i hi
    simp only [representatives, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [left_spec]
    simp only [key]
    have := i.isLt
    omega
  · intro i hi j hj h
    exact Sum.inl.inj h
  · intro x hx
    cases x with
    | inl i => exact ⟨i,Finset.mem_univ _,rfl⟩
    | inr j =>
      simp only [representatives, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [right_spec] at hx
      simp only [key] at hx
      have := (right p j).isLt
      omega
  · intro i hi
    rw [left_spec]

def covariance {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n) (Fin n) R) : Matrix (Vertex n) (Vertex n) R :=
  Matrix.fromBlocks 0 A A.transpose 0

theorem covariance_same_color_zero {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n) (Fin n) R) (x y : Vertex n)
    (h : color x = color y) : covariance A x y = 0 := by
  cases x <;> cases y <;> simp_all [color,covariance]

/-- Full finite pairing sum, with monochromatic pairings included before
zero elimination, equals the permanent. No Gaussian measure is asserted. -/
theorem all_pairings_eq_permanent {n : ℕ} {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n) (Fin n) R) :
    ∑ p : Pairing n, weight (covariance A) p = Matrix.permanent A := by
  classical
  rw [sum_eq_bipartite_filter _ (covariance_same_color_zero A)]
  rw [Finset.sum_subtype (p := Bipartite) _ (by intro p; simp) (fun p => weight (covariance A) p)]
  calc
    ∑ p : BP n, weight (covariance A) p.val =
        ∑ p : BP n, BipartitePairingPermanent.weight A (toPairing p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [weight_eq_left_product]
      rfl
    _ = BipartitePairingPermanent.pairingSum A :=
      Fintype.sum_equiv (WickBipartiteEquiv.pairingEquiv n) _ _ (fun p => rfl)
    _ = Matrix.permanent A := BipartitePairingPermanent.pairingSum_eq_permanent A

theorem empty_pairing_sum {R : Type*} [CommSemiring R]
    (A : Matrix (Fin 0) (Fin 0) R) :
    ∑ p : Pairing 0, weight (covariance A) p = 1 := by
  rw [all_pairings_eq_permanent]
  exact Matrix.permanent_isEmpty

end WickPairingPermanent
#print axioms WickPairingPermanent.all_pairings_eq_permanent
