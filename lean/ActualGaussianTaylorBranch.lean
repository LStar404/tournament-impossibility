import AnalyticTaylorBranch
import ActualBlockGaussianSource

noncomputable section
namespace ActualGaussianTaylorBranch
open GaussianParameterBranch GaussianScalarFactor DiamondFreeKernelLimit
open Filter Topology BlockGaussianDeterminant

theorem beta_analytic (n : ℕ) : AnalyticAt ℂ (beta n) 0 := by
  unfold beta; fun_prop

theorem log_analytic (n : ℕ) : AnalyticAt ℂ (logBeta n) 0 := by
  exact (beta_analytic n).clog (by simp [beta,Complex.slitPlane])

theorem parameter_analytic (n : ℕ) : AnalyticAt ℂ (parameter n) 0 := by
  have hr : AnalyticAt ℂ (root n) 0 := ((log_analytic n).neg.div_const (c:=2)).cexp'
  exact analyticAt_id.mul hr

theorem prefactor_analytic (n : ℕ) : AnalyticAt ℂ (prefactor n) 0 := by
  exact ((analyticAt_const.mul (log_analytic n)).div_const (c:=2)).cexp'

theorem kernel_analytic (n : ℕ) : AnalyticAt ℂ (fun z => finiteKernel n (parameter n z*Complex.I)) 0 := by
  have hh : AnalyticAt ℂ (finiteKernel n) (parameter n 0*Complex.I) := by
    unfold finiteKernel; fun_prop
  exact hh.comp (f:=fun z => parameter n z*Complex.I) (x:=0) ((parameter_analytic n).mul analyticAt_const)

theorem origin (n : ℕ) : gaussian n 0=1 := by
  simp [gaussian,prefactor,logBeta,beta,parameter,finiteKernel]

theorem gaussian_analytic (n : ℕ) : AnalyticAt ℂ (gaussian n) 0 := by
  apply (prefactor_analytic n).div (kernel_analytic n)
  simp [parameter,finiteKernel]

/-- The actual chosen analytic Gaussian factor has the canonical formal branch
for the doubled tournament block. Only a germ at zero is asserted. -/
theorem actual_branch {n : ℕ} (T : DiamondGap.Tournament (Fin n))
    (hT : T.diamonds.card=0) (v : ℂ) (hv : v^2=1) :
    AnalyticTaylorArithmetic.series (gaussian n) =
      NormalizedDeterminantBranch.branch (AffineMatrixTaylorBridge.formal (blockQ T v)).det := by
  apply AnalyticTaylorBranch.branch_series (blockQ T v) (gaussian n) (gaussian_analytic n) (origin n)
  have hb : ∀ᶠ z in 𝓝 (0:ℂ), beta n z≠0 :=
    (beta_analytic n).continuousAt.eventually_ne (by simp [beta])
  have hh : ∀ᶠ z in 𝓝 (0:ℂ), finiteKernel n (parameter n z*Complex.I)≠0 :=
    (kernel_analytic n).continuousAt.eventually_ne (by simp [parameter,finiteKernel])
  filter_upwards [hb,hh] with z hz hz'
  have hs := ActualBlockGaussianSource.branch_square T hT v z hv hz hz'
  simpa only [block_representation,AffineMatrixTaylorBridge.actual] using hs

end ActualGaussianTaylorBranch
#print axioms ActualGaussianTaylorBranch.actual_branch
