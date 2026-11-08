import DiamondFreeRepresentation
import TournamentHamiltonian.TransitiveDeterminant
import Mathlib

namespace DiamondFreeDeterminant
open Matrix

 theorem det_transitiveSkew (n : ℕ) :
    (TournamentHamiltonian.transitiveSkew n : Matrix (Fin n) (Fin n) ℝ).det =
      (1 + (-1 : ℝ)^n) / 2 := by
  let S : Matrix (Fin n) (Fin n) ℝ := TournamentHamiltonian.transitiveSkew n
  have h (a : ℝ) (ha : a ≠ 0) :
      (a • (1 : Matrix (Fin n) (Fin n) ℝ) + S).det =
        ((a+1)^n + (a-1)^n)/2 := by
    have hm : a • (1 : Matrix (Fin n) (Fin n) ℝ) + S =
        a • TournamentHamiltonian.transitiveKernel n a⁻¹ := by
      simp [TournamentHamiltonian.transitiveKernel, smul_add, smul_smul, ha, S]
    rw [hm, Matrix.det_smul, TournamentHamiltonian.transitiveKernel_det]
    simp only [Fintype.card_fin]
    have h1 : a^n * (1+a⁻¹)^n = (a+1)^n := by
      rw [← mul_pow]; congr 1; field_simp [ha]
    have h2 : a^n * (1-a⁻¹)^n = (a-1)^n := by
      rw [← mul_pow]; congr 1; field_simp [ha]
    calc
      _ = (a^n * (1+a⁻¹)^n + a^n * (1-a⁻¹)^n)/2 := by ring
      _ = _ := by rw [h1,h2]
  have he : (fun a : ℝ => (a • (1 : Matrix (Fin n) (Fin n) ℝ) + S).det) =
      (fun a : ℝ => ((a+1)^n + (a-1)^n)/2) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℝ))
    · fun_prop
    · fun_prop
    · intro a ha
      exact h a ha
  have hz := congrFun he 0
  simpa [S] using hz

open DiamondGap DiamondFreeRepresentation

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def realMatrix (T : Tournament V) : Matrix V V ℝ := fun i j => T.S i j

/-- Sign switching preserves the determinant, not the directed path count. -/
theorem det_switch (T U : Tournament V) (d : V → ℤ)
    (hd : ∀ i, (d i)^2=1)
    (hs : ∀ i j, U.S i j = d i * T.S i j * d j) :
    (realMatrix U).det = (realMatrix T).det := by
  let D : Matrix V V ℝ := Matrix.diagonal (fun i => (d i : ℝ))
  have hm : realMatrix U = D * realMatrix T * D := by
    ext i j
    simp [realMatrix, D, hs, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hh : D * D = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hi : (d i : ℝ)^2 = 1 := by exact_mod_cast hd i
      simpa [D, Matrix.mul_diagonal, Matrix.diagonal_apply, pow_two] using hi
    · simp [D, Matrix.mul_diagonal, Matrix.diagonal_apply, hij, Matrix.one_apply]
  have hdet : D.det * D.det = 1 := by rw [← Matrix.det_mul, hh, Matrix.det_one]
  rw [hm, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = D.det * D.det * (realMatrix T).det := by ring
    _ = _ := by rw [hdet, one_mul]

theorem diamondFree_det (T : Tournament V) (hT : DiamondFree T) :
    (realMatrix T).det = (1 + (-1 : ℝ)^(Fintype.card V))/2 := by
  obtain ⟨d, U, hd, hs, ht⟩ := exists_transitive_switch T hT
  obtain ⟨e, he⟩ := ColorTransport.transitive_tournament_enumeration U ht
  have hm : (realMatrix U).submatrix e e =
      (TournamentHamiltonian.transitiveSkew (Fintype.card V) :
        Matrix (Fin (Fintype.card V)) (Fin (Fintype.card V)) ℝ) := by
    ext i j
    simpa [realMatrix, ColorTransport.orderSign, TournamentHamiltonian.transitiveSkew]
      using he i j
  calc
    _ = (realMatrix U).det := (det_switch T U d hd hs).symm
    _ = ((realMatrix U).submatrix e e).det :=
      (Matrix.det_submatrix_equiv_self e (realMatrix U)).symm
    _ = _ := by rw [hm, det_transitiveSkew]

theorem diamondFree_even_det (T : Tournament V) (hT : DiamondFree T)
    (he : Even (Fintype.card V)) : (realMatrix T).det = 1 := by
  rw [diamondFree_det T hT, he.neg_one_pow]
  norm_num


/-- Induced subtournament along an actual injection. -/
def induced {W : Type*} (T : Tournament V) (f : W → V)
    (hf : Function.Injective f) : Tournament W where
  S i j := T.S (f i) (f j)
  skew i j := T.skew (f i) (f j)
  unit i j hij := T.unit (f i) (f j) (fun h => hij (hf h))

theorem induced_diamondFree {W : Type*} [DecidableEq W]
    (T : Tournament V) (hT : DiamondFree T) (f : W → V)
    (hf : Function.Injective f) : DiamondFree (induced T f hf) := by
  intro s hs
  obtain ⟨_, a,b,c,d,_,hq⟩ := hs
  exact no_quad_nine T hT (f a) (f b) (f c) (f d) hq

/-- Every even principal minor of an actual diamond-free sign matrix is one. -/
theorem diamondFree_even_principal_det (T : Tournament V) (hT : DiamondFree T)
    (s : Finset V) (he : Even s.card) :
    ((realMatrix T).submatrix (Subtype.val : s → V) Subtype.val).det = 1 := by
  exact diamondFree_even_det (induced T Subtype.val Subtype.val_injective)
    (induced_diamondFree T hT Subtype.val Subtype.val_injective) (by simpa using he)

end DiamondFreeDeterminant
