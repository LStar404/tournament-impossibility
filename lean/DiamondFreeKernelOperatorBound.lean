import DiamondFreeKernelInverseTransfer
import TransitiveKernelInverseBounds
import MatrixEuclideanEntryBound

noncomputable section
namespace DiamondFreeKernelOperatorBound
open Matrix DiamondGap DiamondFreeKernelDeterminant DiamondFreeRepresentation
open DiamondFreeKernelInverseTransfer TransitiveKernelInverse TransitiveKernelInverseBounds

/-- Dimension-uniform Euclidean operator bound for the actual graph inverse.
The finite determinant lower bound is explicit; no spectral bound is assumed. -/
theorem actual_operator_bound {n : ℕ} (hn : 0<n) (T : Tournament (Fin n))
    (hT : T.diamonds.card=0) (a : ℂ) (R c : ℝ)
    (ha : ‖a‖≤R/(n:ℝ)) (hc : 0<c) (hH : c≤‖H n a‖) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) ((kernel T a)⁻¹)‖ ≤
      (1+R)*Real.exp R/c := by
  cases n with
  | zero => omega
  | succ m =>
    have hnR : (0:ℝ)<(m+1:ℕ) := by positivity
    have hR : 0≤R := by
      have hh := (le_div_iff₀ hnR).mp ha
      exact (mul_nonneg (norm_nonneg a) hnR.le).trans hh
    have hnz : H (m+1) a ≠ 0 := norm_pos_iff.mp (hc.trans_le hH)
    have hr : ∃ (e : Fin (m+1) ≃ Fin (m+1)) (d : Fin (m+1) → ℤ),
        (∀ i, d i^2=1) ∧ ∀ i j,
        (kernel T a)⁻¹ (e i) (e j) = (d (e i):ℂ) *
          (TournamentHamiltonian.transitiveKernel (m+1) a)⁻¹ i j * (d (e j):ℂ) := by
      have h := inverse_entry_representation T (diamondFree_of_card_zero T hT) a
      rw [Fintype.card_fin] at h
      exact h
    obtain ⟨e,d,hd,he⟩ := hr
    have hdsq (i : Fin (m+1)) : (d i : ℂ)^2=1 := by exact_mod_cast hd i
    have hdnorm (i : Fin (m+1)) : ‖(d i : ℂ)‖=1 := by
      have hh := congrArg norm (hdsq i)
      simp only [norm_pow, norm_one] at hh
      nlinarith [norm_nonneg (d i : ℂ)]
    let s : ℂ := (H (m+1) a)⁻¹ * H m a
    have htdiag (i : Fin (m+1)) :
        (TournamentHamiltonian.transitiveKernel (m+1) a)⁻¹ i i=s := by
      rw [inverse_formula m a hnz]
      simp [s, numerator, Matrix.smul_apply, smul_eq_mul]
    have hdiag (i : Fin (m+1)) : (kernel T a)⁻¹ i i=s := by
      obtain ⟨j,rfl⟩ := e.surjective i
      rw [he, htdiag]
      calc
        _ = ((d (e j):ℂ)^2)*s := by ring
        _ = s := by rw [hdsq, one_mul]
    have hs : ‖s‖≤Real.exp R/c := by
      rw [← htdiag (0 : Fin (m+1))]
      exact inverse_diagonal m a R c ha hc hH _
    have hoff (i j : Fin (m+1)) (hij : i≠j) :
        ‖(kernel T a)⁻¹ i j‖≤(R/((m+1:ℕ):ℝ))*Real.exp R/c := by
      obtain ⟨i',rfl⟩ := e.surjective i
      obtain ⟨j',rfl⟩ := e.surjective j
      rw [he]
      simp only [norm_mul, hdnorm, one_mul, mul_one]
      exact inverse_offdiagonal m a R c ha hc hH i' j' (fun h => hij (congrArg e h))
    let E : Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
      (kernel T a)⁻¹ - s • 1
    have hE : ∀ i j, ‖E i j‖≤(R*Real.exp R/c)/((m+1:ℕ):ℝ) := by
      intro i j
      by_cases hij : i=j
      · subst j
        simpa [E,hdiag] using
          (show (0:ℝ)≤(R*Real.exp R/c)/((m+1:ℕ):ℝ) by positivity)
      · have hh := hoff i j hij
        simpa [E,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,hij,
          div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
    have hm : (kernel T a)⁻¹=s • (1:Matrix (Fin (m+1)) (Fin (m+1)) ℂ)+E := by
      simp [E]
    rw [hm]
    have hb := MatrixEuclideanEntryBound.scalar_identity_add_error (show 0 < m+1 by omega)
      s E hs (show 0 ≤ R*Real.exp R/c by positivity) hE
    convert hb using 1; ring

end DiamondFreeKernelOperatorBound
#print axioms DiamondFreeKernelOperatorBound.actual_operator_bound
