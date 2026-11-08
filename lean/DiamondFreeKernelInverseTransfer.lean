import DiamondFreeKernelDeterminant

noncomputable section
namespace DiamondFreeKernelInverseTransfer
open Matrix DiamondGap DiamondFreeRepresentation DiamondFreeKernelDeterminant
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem switched_inverse (T U : Tournament V) (d : V → ℤ)
    (hd : ∀ i, d i^2=1) (hs : ∀ i j, U.S i j=d i*T.S i j*d j) (z : ℂ) :
    (kernel T z)⁻¹ = diagonal (fun i => (d i : ℂ)) * (kernel U z)⁻¹ * diagonal (fun i => (d i : ℂ)) := by
  let D : Matrix V V ℂ := diagonal (fun i => (d i : ℂ))
  have hsq (i : V) : (d i : ℂ)^2=1 := by exact_mod_cast hd i
  have hDD : D*D=1 := by
    ext i j
    by_cases hij : i=j
    · subst j
      simpa [D, diagonal_mul, diagonal_apply, pow_two] using hsq i
    · simp [D, diagonal_mul, hij, one_apply]
  have hi : D⁻¹=D := Matrix.inv_eq_right_inv hDD
  have hS : signMatrix U = D*signMatrix T*D := by
    ext i j
    simp [signMatrix,D,hs,diagonal_mul,mul_diagonal]
  have hK : kernel U z = D*kernel T z*D := by
    simp only [kernel,hS,mul_add,add_mul,mul_one,hDD,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]
  change (kernel T z)⁻¹=D*(kernel U z)⁻¹*D
  rw [hK,Matrix.mul_inv_rev,Matrix.mul_inv_rev,hi]
  simp only [← Matrix.mul_assoc,hDD,one_mul]
  rw [Matrix.mul_assoc,hDD,mul_one]

/-- Sign switching plus ordinary enumeration transfers all inverse entries.
The statement remains valid for totalized inverses even at singular parameters;
subsequent norm/invertibility estimates explicitly exclude those parameters. -/
theorem inverse_entry_representation (T : Tournament V) (hT : DiamondFree T) (z : ℂ) :
    ∃ (e : Fin (Fintype.card V) ≃ V) (d : V → ℤ),
      (∀ i, d i^2=1) ∧ ∀ i j,
      (kernel T z)⁻¹ (e i) (e j) = (d (e i):ℂ) *
        (TournamentHamiltonian.transitiveKernel (Fintype.card V) z)⁻¹ i j * (d (e j):ℂ) := by
  obtain ⟨d,U,hd,hs,ht⟩ := exists_transitive_switch T hT
  obtain ⟨e,he⟩ := ColorTransport.transitive_tournament_enumeration U ht
  have hS : (signMatrix U : Matrix V V ℂ).submatrix e e =
      TournamentHamiltonian.transitiveSkew (Fintype.card V) := by
    ext i j
    have hr := he i j
    simp only [ColorTransport.orderSign] at hr
    change (U.S (e i) (e j) : ℂ) = _
    unfold TournamentHamiltonian.transitiveSkew
    by_cases hij : i < j
    · simp [hij] at hr ⊢
      exact_mod_cast hr
    · by_cases hji : j < i
      · simp [hij,hji] at hr ⊢
        exact_mod_cast hr
      · simp [hij,hji] at hr ⊢
        exact_mod_cast hr
  have hK : (kernel U z).submatrix e e =
      TournamentHamiltonian.transitiveKernel (Fintype.card V) z := by
    simp [kernel,TournamentHamiltonian.transitiveKernel,submatrix_add,submatrix_smul,submatrix_one_equiv,hS]
  have hinv : ((kernel U z)⁻¹).submatrix e e =
      (TournamentHamiltonian.transitiveKernel (Fintype.card V) z)⁻¹ := by
    rw [← Matrix.inv_submatrix_equiv,hK]
  refine ⟨e,d,hd,?_⟩
  intro i j
  rw [switched_inverse T U d hd hs z]
  simp only [diagonal_mul,mul_diagonal]
  have hentry := congrFun (congrFun hinv i) j
  simpa only [submatrix_apply] using congrArg (fun x : ℂ => (d (e i):ℂ)*x*(d (e j):ℂ)) hentry
end DiamondFreeKernelInverseTransfer
#print axioms DiamondFreeKernelInverseTransfer.inverse_entry_representation
