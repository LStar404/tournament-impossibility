import TournamentRawWickAnalytic

noncomputable section
set_option maxHeartbeats 800000
namespace ActualProductWickGerm
open Filter Topology Matrix BlockGaussianDeterminant GaussianParameterBranch
open ActualGaussianTaylorBranch DiamondFreeComplexResolvent

theorem source_decidable {I : Type*} [Fintype I] (d : DecidableEq I)
    (Q : Matrix I I ℂ) (z : ℂ) : RawSourceTaylorBridge.source Q z =
    (letI : DecidableEq I := d
     (1/2:ℂ)*((fun _ : I => (1:ℂ)) ⬝ᵥ
       (((AffineMatrixTaylorBridge.actual Q z-1)*(AffineMatrixTaylorBridge.actual Q z)⁻¹).mulVec (fun _ => 1)))) := by
  have hd : d=Classical.typeDecidableEq I := Subsingleton.elim _ _
  subst d
  rfl

theorem source_eq_raw {n : ℕ} (T : DiamondGap.Tournament (Fin n)) (v z : ℂ) :
    RawSourceTaylorBridge.source (blockQ T v) z=RawBlockSourceIdentity.rawSource (blockMatrix T v z) := by
  rw [source_decidable (inferInstance : DecidableEq (Fin n ⊕ Fin n))]
  unfold RawBlockSourceIdentity.rawSource RawBlockSourceIdentity.ones
  rw [block_representation]
  change (1/2:ℂ)*_=_/2
  unfold AffineMatrixTaylorBridge.actual
  ring

theorem resolvent_analytic {n : ℕ} (T : DiamondGap.Tournament (Fin n)) (i j : Fin n) :
    AnalyticAt ℂ (fun z => resolventMatrix T (parameter n z) i j) 0 := by
  unfold resolventMatrix
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  exact analyticAt_const.add (((parameter_analytic n).div_const (c:=(n:ℂ))).pow 2 |>.mul analyticAt_const)

theorem eventually_unit {n : ℕ} (T : DiamondGap.Tournament (Fin n)) :
    ∀ᶠ z in 𝓝 (0:ℂ), IsUnit (resolventMatrix T (parameter n z)) := by
  have ha := AnalyticTaylorFinite.analytic_det (fun z => resolventMatrix T (parameter n z)) (resolvent_analytic T)
  have h0 : (resolventMatrix T (parameter n 0)).det≠0 := by simp [parameter,resolventMatrix]
  filter_upwards [ha.continuousAt.eventually_ne h0] with z hz
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hz)

theorem eventually_product {n : ℕ} (hn : 0<n) (T : DiamondGap.Tournament (Fin n))
    (v : ℂ) (hv : v^2=1) :
    (fun z => GaussianScalarFactor.gaussian n z * Complex.exp (RawSourceTaylorBridge.source (blockQ T v) z))
      =ᶠ[𝓝 0] GaussianSourceProduct.product T v := by
  have hb : ∀ᶠ z in 𝓝 (0:ℂ), beta n z≠0 :=
    (beta_analytic n).continuousAt.eventually_ne (by simp [beta])
  filter_upwards [hb,eventually_unit T] with z hz hu
  rw [source_eq_raw]
  exact ActualBlockGaussianSource.factor_eq_product hn T v z hv hz hu

/-- The existing actual product has the actual Wick coefficients as a locally
convergent expansion. This does not assert uniform disk radius or finite recovery. -/
def hasSeries {n : ℕ} (hn : 0<n) (T : DiamondGap.Tournament (Fin n))
    (hT : T.diamonds.card=0) (v : ℂ) (hv : v^2=1) :=
  (TournamentRawWickAnalytic.hasSeries T hT v hv).congr (eventually_product hn T v hv)

end ActualProductWickGerm
#check ActualProductWickGerm.hasSeries
#print axioms ActualProductWickGerm.hasSeries
