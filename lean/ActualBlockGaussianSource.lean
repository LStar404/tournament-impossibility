import BlockGaussianDeterminant
import BlockGaussianSourceElimination
import ComplexSkewSourceIdentity
import RawBlockSourceIdentity
import RawGaussianSourceScalar
import GaussianSourceProduct

noncomputable section
namespace ActualBlockGaussianSource
open Matrix DiamondGap DiamondFreeKernelDeterminant DiamondFreeComplexResolvent
open GaussianParameterBranch BlockGaussianDeterminant RawBlockSourceIdentity

/-- The actual block inverse supplies the solution used in finite elimination. -/
lemma sumSolution_eq {n : ℕ} (T : Tournament (Fin n)) (v z : ℂ)
    (hv : v^2=1) (hb : beta n z≠0)
    (hA : IsUnit (resolventMatrix T (parameter n z))) :
    sumSolution (blockMatrix T v z) =
      (2/(1+v*(z/(n:ℂ)))) •
        ((resolventMatrix T (parameter n z))⁻¹).mulVec (fun _ => 1) := by
  let B := blockMatrix T v z
  let q := B⁻¹.mulVec (ones n)
  let x : Fin n → ℂ := fun i => q (Sum.inl i)
  let y : Fin n → ℂ := fun i => q (Sum.inr i)
  have hq : Sum.elim x y=q := by ext i; cases i <;> rfl
  have hB := (inverse_left_right T v z hv hb hA).1
  have hs : (BlockGaussianSourceElimination.blockSystem (signMatrix T) (z/(n:ℂ)) v).mulVec
      (Sum.elim x y)=Sum.elim (fun _ => 1) (fun _ => 1) := by
    rw [hq]
    change B.mulVec (B⁻¹.mulVec (ones n))= _
    rw [Matrix.mulVec_mulVec,hB,Matrix.one_mulVec]
    ext i; cases i <;> rfl
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hl := Matrix.nonsing_inv_mul (resolventMatrix T (parameter n z)) hu
  have ht : beta n z*(parameter n z/(n:ℂ))^2=(z/(n:ℂ))^2 := by
    have hh := root_identity n z hb
    unfold parameter
    calc
      _ = (z/(n:ℂ))^2*((root n z)^2*beta n z) := by ring
      _ = _ := by rw [hh,mul_one]
  exact BlockGaussianSourceElimination.eliminate_block (signMatrix T)
    ((resolventMatrix T (parameter n z))⁻¹) (z/(n:ℂ)) v (beta n z)
    ((parameter n z/(n:ℂ))^2) x y (fun _ => 1)
    hv rfl hb ht hl hs

/-- Exact raw bilinear source equality, derived from the genuine 2n-dimensional
block inverse rather than assuming its eliminated form. -/
theorem rawSource_eq_actualExponent {n : ℕ} (hn : 0<n)
    (T : Tournament (Fin n)) (v z : ℂ) (hv : v^2=1) (hb : beta n z≠0)
    (hA : IsUnit (resolventMatrix T (parameter n z))) :
    rawSource (blockMatrix T v z)=ActualGaussianSourceExponent.actualExponent T v z := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hl := Matrix.nonsing_inv_mul (resolventMatrix T (parameter n z)) hu
  have hr := Matrix.mul_nonsing_inv (resolventMatrix T (parameter n z)) hu
  have hsource := ComplexSkewSourceIdentity.ones_source (signMatrix T)
    ((resolventMatrix T (parameter n z))⁻¹) ((parameter n z/(n:ℂ))^2)
    (sign_transpose T) hl hr
  have hcontract : (fun _ : Fin n => (1:ℂ)) ⬝ᵥ
      ((resolventMatrix T (parameter n z))⁻¹).mulVec (fun _ => 1) =
      (n:ℂ)+(parameter n z/(n:ℂ))^2 * ActualComplexScoreSource.source T (parameter n z) := by
    simpa only [Fintype.card_fin,ActualComplexScoreSource.source,
      ActualComplexScoreSource.complexScore_eq_mulVec] using hsource
  rw [source_eq_reduced _ (inverse_left_right T v z hv hb hA).1,
    sumSolution_eq T v z hv hb hA, dotProduct_smul, hcontract]
  calc
    _ = RawGaussianSourceScalar.reducedSource n v z (parameter n z)
        (ActualComplexScoreSource.source T (parameter n z)) := by
      unfold RawGaussianSourceScalar.reducedSource
      simp only [smul_eq_mul]
      ring
    _ = _ := RawGaussianSourceScalar.reducedSource_eq_actualExponent hn T v z hv hb

/-- The same scalar Gaussian branch normalizes the actual block determinant. -/
theorem branch_square {n : ℕ} (T : Tournament (Fin n)) (hT : T.diamonds.card=0)
    (v z : ℂ) (hv : v^2=1) (hb : beta n z≠0)
    (hH : DiamondFreeKernelLimit.finiteKernel n (parameter n z*Complex.I)≠0) :
    (GaussianScalarFactor.gaussian n z)^2*(blockMatrix T v z).det=1 := by
  rw [determinant T v z hv]
  exact GaussianDeterminantBranch.gaussian_branch_square T hT z hb hH
/-- The origin-normalized scalar branch times the genuine raw block source
is the product whose uniform estimates have already been proved. This does not
assert a pointwise principal-square-root or a Gaussian integral identity. -/
theorem factor_eq_product {n : ℕ} (hn : 0<n)
    (T : Tournament (Fin n)) (v z : ℂ) (hv : v^2=1) (hb : beta n z≠0)
    (hA : IsUnit (resolventMatrix T (parameter n z))) :
    GaussianScalarFactor.gaussian n z * Complex.exp (rawSource (blockMatrix T v z)) =
      GaussianSourceProduct.product T v z := by
  rw [rawSource_eq_actualExponent hn T v z hv hb hA]
  rfl
end ActualBlockGaussianSource
#print axioms ActualBlockGaussianSource.rawSource_eq_actualExponent
#print axioms ActualBlockGaussianSource.branch_square

#print axioms ActualBlockGaussianSource.factor_eq_product
