import GeneratingRankCore
import PrincipalGeneratingFocused
import TournamentHamiltonian.CrossPermanentBounds
import TournamentHamiltonian.DegreeDeletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TournamentHamiltonian
open scoped Classical Topology
open Filter

theorem tournament_generating_det_le {m : ℕ} (T : Tournament m) (n : ℕ)
    (hn : 0 < n) (hmn : m ≤ n) :
    ((1 : Matrix (Fin m) (Fin m) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T)).det ≤
      2 * Real.exp 1 * ((1 : Matrix (Fin m) (Fin m) ℝ) + (1 / (m : ℝ)) • signMatrix T).det := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  by_cases hm : m = 0
  · subst m
    simp only [Matrix.det_isEmpty]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  let a : ℝ := 1 + 1 / (n : ℝ)
  let b : ℝ := 1 / ((n : ℝ) + 1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : a * b = 1 / (n : ℝ) := by dsimp [a, b]; field_simp
  have heq : (1 : Matrix (Fin m) (Fin m) ℝ) + (2 / (n : ℝ)) • (1 + adjacency T) =
      a • ((1 : Matrix (Fin m) (Fin m) ℝ) + b • signMatrix T + b • Matrix.of (fun _ _ => (1 : ℝ))) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    simp only [mul_add, ← mul_assoc, hab, mul_one]
    have hw := twice_adjacency T i j
    simp only [Matrix.one_apply]
    dsimp [a]
    linear_combination (1 / (n : ℝ)) * hw
  have haPow : a ^ m ≤ Real.exp 1 := by
    have h := pow_le_pow_left₀ ha (by simpa only [a, add_comm] using Real.add_one_le_exp (1 / (n : ℝ))) m
    rw [← Real.exp_nat_mul] at h
    apply h.trans
    apply Real.exp_le_exp.mpr
    simpa only [div_eq_mul_inv, mul_comm, mul_one, one_mul] using (div_le_one hn0).mpr hmnR
  have hbM : b ≤ 1 / (m : ℝ) := by
    dsimp [b]
    exact one_div_le_one_div_of_le hmpos (by linarith)
  have hS (i j : Fin m) : (b • signMatrix T) i j = -(b • signMatrix T) j i := by
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [signMatrix_skew T i j]
    ring
  have hdet0 := (det_one_add_skew_pos (b • signMatrix T) hS).le
  have hrank := det_one_add_skew_add_ones_le (b • signMatrix T) hS b hb
  have hfac : 1 + b * m ≤ 2 := by
    dsimp [b]
    have h : (m : ℝ) / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    rw [one_div_mul_eq_div]
    linarith
  have hmono := signMatrix_kernel_det_mono T b (1 / (m : ℝ)) hb hbM
  have hinner : ((1 : Matrix (Fin m) (Fin m) ℝ) + b • signMatrix T +
      b • Matrix.of (fun _ _ => (1 : ℝ))).det ≤
      2 * ((1 : Matrix (Fin m) (Fin m) ℝ) + (1 / (m : ℝ)) • signMatrix T).det := by
    apply hrank.trans
    have h := mul_le_mul hmono hfac (by positivity : 0 ≤ 1 + b * m)
      ((det_one_add_skew_pos ((1 / (m : ℝ)) • signMatrix T) (by
        intro i j; simp only [Matrix.smul_apply, smul_eq_mul]; rw [signMatrix_skew T i j]; ring)).le)
    simpa only [Fintype.card_fin] using h.trans_eq (mul_comm _ _)
  rw [heq, Matrix.det_smul, Fintype.card_fin]
  have hD0 : 0 ≤ ((1 : Matrix (Fin m) (Fin m) ℝ) + (1 / (m : ℝ)) • signMatrix T).det :=
    (det_one_add_skew_pos _ (by intro i j; simp only [Matrix.smul_apply, smul_eq_mul]; rw [signMatrix_skew T i j]; ring)).le
  have h := mul_le_mul_of_nonneg_left hinner (pow_nonneg ha m)
  apply h.trans
  have hh := mul_le_mul_of_nonneg_right haPow (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hD0)
  simpa only [mul_left_comm, mul_assoc] using hh

theorem core_principalWeight_generating_det {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) (z : ℝ) :
    ((1 : Matrix U U ℝ) + z • (1 + (adjacency T).submatrix Subtype.val Subtype.val)).det =
      ∑ V ∈ U.powerset, z ^ V.card * (principalWeightMatrix T V).det := by
  rw [matrix_principal_generating_det]
  have hlocal (t : Finset U) :
      z ^ t.card * (((1 : Matrix U U ℝ) + (adjacency T).submatrix Subtype.val Subtype.val).submatrix
        (Subtype.val : t → U) Subtype.val).det =
      z ^ (t.map (Function.Embedding.subtype _)).card *
        (principalWeightMatrix T (t.map (Function.Embedding.subtype _))).det := by
    simp only [Finset.card_map]
    congr 1
    let e := t.equivMap (Function.Embedding.subtype _)
    have heval (i : t) : ((e i : t.map (Function.Embedding.subtype _)) : Fin n) = i.val.val := rfl
    have heq : (principalWeightMatrix T (t.map (Function.Embedding.subtype _))).submatrix e e =
        ((1 : Matrix U U ℝ) + (adjacency T).submatrix Subtype.val Subtype.val).submatrix
          (Subtype.val : t → U) Subtype.val := by
      ext i j
      simp only [principalWeightMatrix, Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply,
        heval, Subtype.ext_iff]
    rw [← heq, Matrix.det_submatrix_equiv_self]
  simp_rw [hlocal]
  exact sum_finsets_subtype_eq_powerset U (fun V => z ^ V.card * (principalWeightMatrix T V).det)

theorem core_principalWeight_generating_eq_induced {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) (z : ℝ) :
    (∑ V ∈ U.powerset, z ^ V.card * (principalWeightMatrix T V).det) =
      ((1 : Matrix (Fin U.card) (Fin U.card) ℝ) + z • (1 + adjacency (inducedTournament T U))).det := by
  rw [← core_principalWeight_generating_det]
  have hmat : ((1 : Matrix U U ℝ) + z • (1 + (adjacency T).submatrix Subtype.val Subtype.val)).submatrix
      (subsetVertexEquiv U) (subsetVertexEquiv U) =
      (1 : Matrix (Fin U.card) (Fin U.card) ℝ) + z • (1 + adjacency (inducedTournament T U)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      (subsetVertexEquiv U).injective.eq_iff, adjacency_inducedTournament]
  rw [← hmat, Matrix.det_submatrix_equiv_self]

theorem core_principalWeight_generating_le {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) (hn : 0 < n) :
    (∑ V ∈ U.powerset, (2 / (n : ℝ)) ^ V.card * (principalWeightMatrix T V).det) ≤
      2 * Real.exp 1 * ((1 : Matrix (Fin U.card) (Fin U.card) ℝ) +
        (1 / (U.card : ℝ)) • signMatrix (inducedTournament T U)).det := by
  rw [core_principalWeight_generating_eq_induced]
  exact tournament_generating_det_le _ n hn (by simpa using U.card_le_univ)

end TournamentHamiltonian

set_option pp.fullNames true
#check TournamentHamiltonian.tournament_generating_det_le
#print axioms TournamentHamiltonian.tournament_generating_det_le
#check TournamentHamiltonian.core_principalWeight_generating_det
#print axioms TournamentHamiltonian.core_principalWeight_generating_det
#check TournamentHamiltonian.core_principalWeight_generating_eq_induced
#print axioms TournamentHamiltonian.core_principalWeight_generating_eq_induced
#check TournamentHamiltonian.core_principalWeight_generating_le
#print axioms TournamentHamiltonian.core_principalWeight_generating_le
