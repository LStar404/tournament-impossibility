import RealGaugeSolution

set_option autoImplicit false
noncomputable section
namespace RealGaugeOperator
open Matrix Finset DenseResolventRowBound BalancedHessianInverse RealGaugeSolution
variable {m : ℕ}

/-- The original Neumann construction, exposed as a single bounded linear map. -/
theorem complex_inverse_operator (hm : 0 < m)
    (Q E : Matrix (Block m) (Block m) ℂ) {C q d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q‖ ≤ q) (hq : q < 1)
    (he : ∀ i j, ‖Q i j‖ ≤ C/(m : ℝ)) (hb : Balanced Q)
    (hE : ∀ i, (∑ j, ‖E i j‖) ≤ d)
    (hsmall : inverseConstant C q * d ≤ 1/2) :
    ∃ T : (Block m → ℂ) →L[ℂ] (Block m → ℂ),
      infinityMap (baseline Q + E) * T = 1 ∧
      T * infinityMap (baseline Q + E) = 1 ∧
      ‖T‖ ≤ 2 * inverseConstant C q := by
  let A := infinityMap (baseline Q)
  let L := infinityMap (baseInverse Q)
  let D := infinityMap E
  let F := L * D
  let N := neumann F
  let T := N * L
  have hi := base_inverse_data hm Q hQ hq hb
  have hAL : A*L = 1 := by
    change infinityMap (baseline Q) * infinityMap (baseInverse Q) = 1
    rw [← infinityMap_mul, hi.2, infinityMap_one]
  have hLA : L*A = 1 := by
    change infinityMap (baseInverse Q) * infinityMap (baseline Q) = 1
    rw [← infinityMap_mul, hi.1, infinityMap_one]
  have hK : 0 ≤ inverseConstant C q := by
    have hnon := entryConstant_nonneg hC hq
    unfold inverseConstant rowConstant
    positivity
  have hL : ‖L‖ ≤ inverseConstant C q := base_inverse_infinity_bound hm Q hC hQ hq he
  have hD : ‖D‖ ≤ d := infinityMap_norm_le E hd hE
  have hF : ‖F‖ ≤ inverseConstant C q*d :=
    (norm_mul_le L D).trans (mul_le_mul hL hD (norm_nonneg D) hK)
  have hn := neumann_data F hF (by linarith : inverseConstant C q*d < 1)
  have hN : ‖N‖ ≤ 2 := by
    apply hn.2.2.trans
    apply (div_le_iff₀ (by linarith : 0 < 1-inverseConstant C q*d)).mpr
    linarith
  have hfactor : A+D = A*(1+F) := by
    change A+D = A*(1+L*D)
    rw [mul_add, mul_one, ← mul_assoc, hAL, one_mul]
  have hJT : (A+D)*T = 1 := by
    change (A+D)*(N*L) = 1
    rw [hfactor, mul_assoc, ← mul_assoc (1+F) N L, hn.1, one_mul, hAL]
  have hT : ‖T‖ ≤ 2*inverseConstant C q :=
    (norm_mul_le N L).trans (mul_le_mul hN hL (norm_nonneg L) (by norm_num))
  have hTJ : T*(A+D) = 1 := by
    change (N*L)*(A+D) = 1
    rw [hfactor, ← mul_assoc, mul_assoc N L A, hLA, mul_one, hn.2.1]
  exact ⟨T, by simpa only [infinityMap_add] using hJT,
    by simpa only [infinityMap_add] using hTJ, hT⟩

/-- Ordinary function-space infinity operator norm. -/
def realInfinityMap (A : Matrix (Block m) (Block m) ℝ) :
    (Block m → ℝ) →L[ℝ] (Block m → ℝ) :=
  ContinuousLinearMap.mk (Matrix.mulVecLin A)

@[simp] lemma realInfinityMap_apply (A : Matrix (Block m) (Block m) ℝ)
    (x : Block m → ℝ) : realInfinityMap A x = A *ᵥ x := rfl

lemma complexify_add (A B : Matrix (Block m) (Block m) ℝ) :
    complexify (A+B) = complexify A + complexify B := by
  ext i j
  simp [complexify]

lemma complexify_gauge : complexify (realGauge m) = BalancedHessianInverse.gauge m := by
  ext i j
  cases i <;> cases j <;> simp [complexify, realGauge, BalancedHessianInverse.gauge, realSign, sign]

/-- A fixed real inverse matrix, rather than a RHS-dependent choice of solution. -/
theorem real_inverse_matrix (hm : 0 < m)
    (Q E : Matrix (Block m) (Block m) ℝ) {C q d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (complexify Q)‖ ≤ q) (hq : q < 1)
    (he : ∀ i j, ‖Q i j‖ ≤ C/(m : ℝ)) (hb : Balanced (complexify Q))
    (hE : ∀ i, (∑ j, ‖E i j‖) ≤ d)
    (hGE : BalancedHessianInverse.gauge m * complexify E = 0)
    (hsmall : inverseConstant C q * d ≤ 1/2) :
    let J := realModel Q + E + realGauge m
    let L := J⁻¹
    L * J = 1 ∧ J * L = 1 ∧
      ‖realInfinityMap L‖ ≤ 2 * inverseConstant C q ∧
      realGauge m * L = realGauge m := by
  let J := realModel Q + E + realGauge m
  have hJC : complexify J = baseline (complexify Q) + complexify E := by
    dsimp [J]
    rw [complexify_add, complexify_add, complexify_model, complexify_gauge]
    unfold model baseline
    abel
  have heC : ∀ i j, ‖complexify Q i j‖ ≤ C/(m : ℝ) := by
    simpa only [complexify, Complex.norm_real] using he
  have hEC : ∀ i, (∑ j, ‖complexify E i j‖) ≤ d := by
    simpa only [complexify, Complex.norm_real] using hE
  obtain ⟨T, hJT, hTJ, hT⟩ := complex_inverse_operator hm (complexify Q)
    (complexify E) hC hd hQ hq heC hb hEC hsmall
  have hsolve (w : Block m → ℝ) :
      J *ᵥ (fun i => (T (fun j => (w j : ℂ)) i).re) = w := by
    rw [realPart_mulVec, hJC]
    have hh := congrArg (fun f : (Block m → ℂ) →L[ℂ] (Block m → ℂ) =>
      f (fun j => (w j : ℂ))) hJT
    have hh' : (baseline (complexify Q) + complexify E) *ᵥ
        T (fun j => (w j : ℂ)) = (fun j => (w j : ℂ)) := by simpa [Matrix.add_mulVec] using hh
    rw [hh']
    simp
  have hunit : IsUnit J := Matrix.mulVec_surjective_iff_isUnit.mp
    (fun w => ⟨_, hsolve w⟩)
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hLJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  have hJL : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hdet
  have hK : 0 ≤ 2 * inverseConstant C q := (norm_nonneg T).trans hT
  have heq (w : Block m → ℝ) :
      J⁻¹ *ᵥ w = fun i => (T (fun j => (w j : ℂ)) i).re := by
    calc
      _ = J⁻¹ *ᵥ (J *ᵥ (fun i => (T (fun j => (w j : ℂ)) i).re)) := by rw [hsolve]
      _ = _ := by rw [Matrix.mulVec_mulVec, hLJ, Matrix.one_mulVec]
  have hbound : ‖realInfinityMap J⁻¹‖ ≤ 2 * inverseConstant C q := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro w
    rw [realInfinityMap_apply, heq]
    exact (norm_realPart_le _).trans ((T.le_opNorm _).trans
      (by simpa only [norm_complexify_vec] using
        mul_le_mul_of_nonneg_right hT (norm_nonneg (fun j => (w j : ℂ)))))
  have hGJC : BalancedHessianInverse.gauge m * complexify J = BalancedHessianInverse.gauge m := by
    rw [hJC]
    have hh := model_gauge_left hm (complexify Q) hb
    have hbJ : baseline (complexify Q) = model (complexify Q) + BalancedHessianInverse.gauge m := by
      unfold model baseline
      abel
    rw [hbJ, mul_add, mul_add, hh, gauge_square hm, hGE]
    simp
  have hGJ : realGauge m * J = realGauge m := by
    ext i j
    have hh := congrArg (fun A : Matrix (Block m) (Block m) ℂ => (A i j).re) hGJC
    rw [← complexify_gauge] at hh
    simpa [Matrix.mul_apply, complexify, Complex.mul_re] using hh
  have hGL : realGauge m * J⁻¹ = realGauge m := by
    calc
      _ = (realGauge m * J) * J⁻¹ := by rw [hGJ]
      _ = _ := by rw [mul_assoc, hJL, mul_one]
  exact ⟨hLJ, hJL, hbound, hGL⟩

end RealGaugeOperator
#print axioms RealGaugeOperator.complex_inverse_operator
#print axioms RealGaugeOperator.real_inverse_matrix
