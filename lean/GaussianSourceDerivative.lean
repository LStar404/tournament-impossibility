import GaussianSourceProduct
import GaussianSourceAnalytic
import ComplexCauchyErrorTransfer

noncomputable section
open Filter Topology DiamondGap
namespace GaussianSourceDerivative

def middleRadius (r R : ℝ) : ℝ := (r+R)/2

def derivativeConstant (j : ℕ) (r R K : ℝ) : ℝ :=
  (j.factorial : ℝ)*GaussianSourceProduct.errorConstant (middleRadius r R) R K /
    ((middleRadius r R-r)/2)^j

/-- Every fixed complex derivative of the actual assembled product has a
uniform O(1/n) error on the smaller disk. Analyticity and the larger-disk
value estimate are discharged from the actual graph-level theorems. -/
theorem eventually_uniform_derivative (j : ℕ) {r R K : ℝ}
    (hr : 0 ≤ r) (hrR : r<R) (hpi : R<Real.pi/2) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament (Fin n), T.diamonds.card=0 →
      ActualComplexScoreSource.scoreEnergy T ≤ K*(n:ℝ) →
      ∀ (v z : ℂ), ‖v‖ ≤ 1 → ‖z‖ ≤ r →
        ‖iteratedDeriv j (GaussianSourceProduct.product T v) z-
          iteratedDeriv j (GaussianSourceProduct.target v) z‖ ≤ 
          derivativeConstant j r R K/(n:ℝ) := by
  let r0 := middleRadius r R
  have hr0 : 0 ≤ r0 := by dsimp [r0,middleRadius]; linarith
  have hgap : r<r0 := by dsimp [r0,middleRadius]; linarith
  have hr0R : r0<R := by dsimp [r0,middleRadius]; linarith
  filter_upwards [GaussianSourceProduct.eventually_uniform_error hr0 hr0R hpi hK,
    GaussianSourceAnalytic.eventually_differentiable_disk hr0 hr0R hpi]
    with n hvalue hanalytic
  intro T hT henergy v z hv hz
  have hd := hanalytic T hT v hv
  have hb : ∀ w ∈ Metric.ball (0:ℂ) r0,
      ‖GaussianSourceProduct.product T v w-GaussianSourceProduct.target v w‖ ≤ 
        GaussianSourceProduct.errorConstant r0 R K/(n:ℝ) := by
    intro w hw
    have hwr : ‖w‖ ≤ r0 := (by simpa using hw : ‖w‖<r0).le
    exact hvalue T hT henergy w v hwr hv
  have h := ComplexCauchyErrorTransfer.derivative_difference_half_gap
    (GaussianSourceProduct.product T v) (GaussianSourceProduct.target v)
    hgap hd.1 hd.2 n j hb hz
  convert h using 1
  unfold derivativeConstant
  dsimp [r0]
  ring

theorem derivativeConstant_nonneg (j : ℕ) {r R K : ℝ}
    (hr : 0 ≤ r) (hrR : r<R) (hpi : R<Real.pi/2) (hK : 0 ≤ K) :
    0 ≤ derivativeConstant j r R K := by
  have hr0 : 0 ≤ middleRadius r R := by unfold middleRadius; linarith
  have hr0R : middleRadius r R<R := by unfold middleRadius; linarith
  have hgap : 0 < (middleRadius r R-r)/2 := by unfold middleRadius; linarith
  obtain ⟨C,hC,hEq,_⟩ := GaussianSourceProduct.exists_uniform_constant hr0 hr0R hpi hK
  have hvalue : 0 ≤ GaussianSourceProduct.errorConstant (middleRadius r R) R K := by
    rw [← hEq]
    exact hC
  unfold derivativeConstant
  positivity

/-- The explicit constant is independent of n, graph, v and the point in the
inner disk. This concerns the branch-defined product, not an unproved equality
to a raw Gaussian integral or permanent-recovery expression. -/
theorem exists_uniform_derivative_constant (j : ℕ) {r R K : ℝ}
    (hr : 0 ≤ r) (hrR : r<R) (hpi : R<Real.pi/2) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ C=derivativeConstant j r R K ∧
      ∀ᶠ n : ℕ in atTop, ∀ T : Tournament (Fin n), T.diamonds.card=0 →
        ActualComplexScoreSource.scoreEnergy T ≤ K*(n:ℝ) →
        ∀ (v z : ℂ), ‖v‖ ≤ 1 → ‖z‖ ≤ r →
          ‖iteratedDeriv j (GaussianSourceProduct.product T v) z-
            iteratedDeriv j (GaussianSourceProduct.target v) z‖ ≤ C/(n:ℝ) :=
  ⟨derivativeConstant j r R K,derivativeConstant_nonneg j hr hrR hpi hK,rfl,
    eventually_uniform_derivative j hr hrR hpi hK⟩

end GaussianSourceDerivative
#print axioms GaussianSourceDerivative.eventually_uniform_derivative
#print axioms GaussianSourceDerivative.exists_uniform_derivative_constant
