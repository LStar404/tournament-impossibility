import PermanentCircleSpectralCoordinates
noncomputable section
namespace PermanentSpectralFrame
open Matrix
variable {n : ℕ}

def rankOne (u w : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j => u i*w j
lemma rankOne_mulVec (u w x : Fin n → ℂ) :
    rankOne u w*ᵥx = (w ⬝ᵥ x) • u := by
  ext i
  simp only [rankOne, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    ← Finset.mul_sum, mul_assoc]
  ring

/-- Exact spectral coordinate gap in the kernel of the rank-one part. -/
lemma kernel_energy_bound (u w : Fin n → ℂ) (E : Matrix (Fin n) (Fin n) ℂ)
    (q : ℝ) (hq : 0≤q) (hE : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) E‖≤q)
    (c : Fin n → ℂ)
    (hk : w ⬝ᵥ ((frame (rankOne u w+E):Matrix (Fin n) (Fin n) ℂ)*ᵥc)=0) :
    (∑i, eigenvalue (rankOne u w+E) i*‖c i‖^2) ≤ q^2*∑i,‖c i‖^2 := by
  let A := rankOne u w+E
  let x := (frame A:Matrix (Fin n) (Fin n) ℂ)*ᵥc
  have hx : A*ᵥx=E*ᵥx := by
    change (rankOne u w+E)*ᵥx=E*ᵥx
    rw [Matrix.add_mulVec, rankOne_mulVec, hk, zero_smul, zero_add]
  have h := matrix_operator_energy E q hq hE x
  rw [← hx] at h
  rw [image_frame_energy, frame_energy] at h
  exact h

lemma two_coordinate_energy (f : Fin n → ℝ) (i j : Fin n) (hij : i≠j) (a b : ℂ) :
    (∑k, f k*‖((Pi.single i a : Fin n → ℂ)+(Pi.single j b : Fin n → ℂ)) k‖^2) =
      f i*‖a‖^2+f j*‖b‖^2 := by
  classical
  have hpoint (k : Fin n) :
      f k * ‖((Pi.single i a : Fin n → ℂ) + (Pi.single j b : Fin n → ℂ)) k‖ ^ 2 =
        (Pi.single i (f i * ‖a‖ ^ 2) : Fin n → ℝ) k +
        (Pi.single j (f j * ‖b‖ ^ 2) : Fin n → ℝ) k := by
    by_cases hki : k = i
    · subst k
      simp [hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst k
        simp [hij, Ne.symm hij]
      · simp [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

/-- Two actual Gram eigenvalues above q² are impossible after a rank-one perturbation. -/
theorem bad_indices_equal (u w : Fin n → ℂ) (E : Matrix (Fin n) (Fin n) ℂ)
    (q : ℝ) (hq : 0≤q) (hE : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) E‖≤q)
    (i j : Fin n) (hi : q^2<eigenvalue (rankOne u w+E) i)
    (hj : q^2<eigenvalue (rankOne u w+E) j) : i=j := by
  classical
  by_contra hij
  let A := rankOne u w+E
  let vi := (frame A:Matrix (Fin n) (Fin n) ℂ)*ᵥ(Pi.single i 1)
  let vj := (frame A:Matrix (Fin n) (Fin n) ℂ)*ᵥ(Pi.single j 1)
  let elli := w ⬝ᵥ vi
  let ellj := w ⬝ᵥ vj
  have lift (a b : ℂ) :
      w ⬝ᵥ ((frame A:Matrix (Fin n) (Fin n) ℂ)*ᵥ((Pi.single i a : Fin n → ℂ)+(Pi.single j b : Fin n → ℂ))) =
        a*elli+b*ellj := by
    simp [elli,ellj,vi,vj,Matrix.mulVec_add,Matrix.mulVec_single,dotProduct,
      mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm]
  by_cases hz : elli=0
  · have hk := kernel_energy_bound u w E q hq hE (Pi.single i 1+Pi.single j 0)
      (by rw [lift,hz]; ring)
    rw [two_coordinate_energy _ i j hij] at hk
    have hn := two_coordinate_energy (fun _ => (1:ℝ)) i j hij 1 0
    simp only [one_mul] at hn
    rw [hn] at hk
    simp at hk
    linarith
  · have hk := kernel_energy_bound u w E q hq hE (Pi.single i (-ellj)+Pi.single j elli)
      (by rw [lift]; ring)
    rw [two_coordinate_energy _ i j hij] at hk
    have hn := two_coordinate_energy (fun _ => (1:ℝ)) i j hij (-ellj) elli
    simp only [one_mul] at hn
    rw [hn] at hk
    have hp : 0<‖elli‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    have ha : 0≤‖-ellj‖^2 := sq_nonneg _
    nlinarith

theorem bad_card_le_one (u w : Fin n → ℂ) (E : Matrix (Fin n) (Fin n) ℂ)
    (q : ℝ) (hq : 0≤q) (hE : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) E‖≤q) :
    (Finset.univ.filter (fun i => q^2<eigenvalue (rankOne u w+E) i)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact bad_indices_equal u w E q hq hE i j (Finset.mem_filter.mp hi).2
    (Finset.mem_filter.mp hj).2
end PermanentSpectralFrame
#print axioms PermanentSpectralFrame.bad_card_le_one
