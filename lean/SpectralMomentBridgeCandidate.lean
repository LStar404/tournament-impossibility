import TournamentHamiltonian.SkewSpectrum
import ActualMomentAdapterCandidate

/-!
Isolated spectral moment bridge, compiled and separately audited.
No frozen project sources or manifests were edited.
-/

open scoped Matrix BigOperators

namespace SpectralMomentBridgeCandidate
open TournamentHamiltonian

private theorem trace_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U M).trace = M.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, Unitary.coe_star_mul_self, one_mul]

private theorem complex_pow_entry {n : ℕ} (T : Tournament n) (r : ℕ)
    (i j : Fin n) :
    (complexSignMatrix T ^ r) i j = ((signMatrix T ^ r) i j : ℂ) := by
  have h := Matrix.map_pow (signMatrix T) Complex.ofRealHom r
  exact (congrArg (fun M => M i j) h).symm

/-- Frobenius powers are the even frequency moments, including at r = 0. -/
theorem frobenius_power_eq_frequency {n : ℕ} (T : Tournament n) (r : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, ((signMatrix T ^ r) i j) ^ 2) =
      ∑ i : Fin n, skewFrequency T i ^ (2 * r) := by
  classical
  let U := (skewHermitian_isHermitian T).eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => -Complex.I * (skewFrequency T i : ℂ))
  have hdiag : complexSignMatrix T = Unitary.conjStarAlgAut ℂ _ U D :=
    complexSignMatrix_unitary_diagonalization T
  have hp : complexSignMatrix T ^ r = Unitary.conjStarAlgAut ℂ _ U (D ^ r) := by
    rw [map_pow, ← hdiag]
  have hd : (D ^ r).conjTranspose * D ^ r =
      Matrix.diagonal (fun i => (skewFrequency T i : ℂ) ^ (2 * r)) := by
    simp only [D, Matrix.diagonal_pow, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hb : star (-Complex.I * (skewFrequency T i : ℂ)) *
        (-Complex.I * (skewFrequency T i : ℂ)) = (skewFrequency T i : ℂ) ^ 2 := by
      simp [mul_comm, mul_left_comm, pow_two]
      rw [← mul_assoc, Complex.I_mul_I]
      simp
    change star ((-Complex.I * (skewFrequency T i : ℂ)) ^ r) *
      (-Complex.I * (skewFrequency T i : ℂ)) ^ r = _
    rw [star_pow, ← mul_pow, hb, ← pow_mul]
  have ht : ((complexSignMatrix T ^ r).conjTranspose * complexSignMatrix T ^ r).trace =
      ∑ i : Fin n, (skewFrequency T i : ℂ) ^ (2 * r) := by
    rw [hp]
    change (star (Unitary.conjStarAlgAut ℂ _ U (D ^ r)) *
      Unitary.conjStarAlgAut ℂ _ U (D ^ r)).trace = _
    rw [← map_star, ← map_mul, trace_conjugation]
    change ((D ^ r).conjTranspose * D ^ r).trace = _
    rw [hd, Matrix.trace_diagonal]
  have he : ((complexSignMatrix T ^ r).conjTranspose * complexSignMatrix T ^ r).trace =
      ∑ i : Fin n, ∑ j : Fin n, (((signMatrix T ^ r) i j) ^ 2 : ℝ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, complex_pow_entry, Complex.star_def,
      Complex.conj_ofReal, pow_two]
    push_cast
    exact Finset.sum_comm
  rw [he] at ht
  exact_mod_cast ht

/-- Zero frequencies contribute zero only for positive powers. -/
theorem frequency_even_moment_pairing {n : ℕ} (T : Tournament n)
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ i : Fin n, skewFrequency T i ^ (2 * r)) =
      2 * ((positiveSkewFrequencies T).map (fun x => x ^ (2 * r))).sum := by
  classical
  let M := Finset.univ.val.map (skewFrequency T)
  have he : 2 * r ≠ 0 := by omega
  have hz : ((M.filter (fun x => x = 0)).map (fun x => x ^ (2 * r))).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    simp only [Multiset.mem_filter] at hx
    simp [hx.2, he]
  have hneg : (((positiveSkewFrequencies T).map (fun x => -x)).map
      (fun x => x ^ (2 * r))).sum =
      ((positiveSkewFrequencies T).map (fun x => x ^ (2 * r))).sum := by
    simp [Multiset.map_map, pow_mul]
  have hs : (M.map (fun x => x ^ (2 * r))).sum =
      ∑ i : Fin n, skewFrequency T i ^ (2 * r) := by
    simp only [M, Multiset.map_map, Function.comp_def, Finset.sum_map_val]
  have h := skewFrequency_multiset_decomposition T
  change M = _ at h
  rw [h, Multiset.map_add, Multiset.map_add, Multiset.sum_add,
    Multiset.sum_add, hneg, hz] at hs
  linarith

private theorem paired_moment_scale {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (r : ℕ) :
    (n : ℝ) ^ (2 * r) * ((pairedMasses T).map (fun x => x ^ r)).sum =
      ((positiveSkewFrequencies T).map (fun x => x ^ (2 * r))).sum := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl : ∀ L : List ℝ, (L.map (fun x => x ^ r)).sum =
      ((L : Multiset ℝ).map (fun x => x ^ r)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih => simpa using congrArg (fun y => a ^ r + y) ih
  rw [hl]
  unfold pairedMasses
  rw [Multiset.coe_toList, Multiset.map_map]
  change (n : ℝ) ^ (2 * r) *
    ((positiveSkewFrequencies T).map (fun x => (x ^ 2 / (n : ℝ) ^ 2) ^ r)).sum = _
  have hx (x : ℝ) : (n : ℝ) ^ (2 * r) * (x ^ 2 / (n : ℝ) ^ 2) ^ r =
      x ^ (2 * r) := by
    rw [div_pow, ← pow_mul, ← pow_mul]
    field_simp [hnR]
  induction positiveSkewFrequencies T using Multiset.induction_on with
  | empty => simp
  | cons a M ih => simp only [Multiset.map_cons, Multiset.sum_cons, mul_add, hx, ih]

theorem frobenius_power_eq_paired_moment {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (r : ℕ) (hr : 1 ≤ r) :
    (∑ i : Fin n, ∑ j : Fin n, ((signMatrix T ^ r) i j) ^ 2) =
      2 * (n : ℝ) ^ (2 * r) * ((pairedMasses T).map (fun x => x ^ r)).sum := by
  rw [frobenius_power_eq_frequency, frequency_even_moment_pairing T r hr,
    mul_assoc, paired_moment_scale T hn r]

theorem paired_moments_le_transitive {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (r : ℕ) (hr : 1 ≤ r) :
    ((pairedMasses T).map (fun x => x ^ r)).sum ≤
      ((pairedMasses (transitiveTournament n)).map (fun x => x ^ r)).sum := by
  have h := ActualMomentAdapterCandidate.actual_frobenius_moments_le_transitive T r
  rw [frobenius_power_eq_paired_moment T hn r hr,
    frobenius_power_eq_paired_moment (transitiveTournament n) hn r hr] at h
  have hc : 0 < 2 * (n : ℝ) ^ (2 * r) := by positivity
  nlinarith

end SpectralMomentBridgeCandidate

#print axioms SpectralMomentBridgeCandidate.frobenius_power_eq_frequency
#print axioms SpectralMomentBridgeCandidate.frobenius_power_eq_paired_moment
#print axioms SpectralMomentBridgeCandidate.paired_moments_le_transitive
