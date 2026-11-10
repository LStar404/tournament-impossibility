import RootPotentialUpperCandidate
import SameRootFrobeniusCandidate
import PhysicalMinorRecoveryCandidate
/-! Verified isolated finite bridges; no reference lower-bound claim. -/
set_option autoImplicit false
noncomputable section
namespace SameRootPotentialCandidate
open Matrix Finset MatrixScalingMassPotential ActualRootEnergy FiniteSymmetricQuadratic
open ActualReconstructionBridgeCandidate SameRootFrobeniusCandidate
open RootPotentialUpperCandidate NonprincipalReconstructionCandidate
open ActualKappaBridgeCandidate TournamentHamiltonian ActualPrescalingNormalization
open DeletedScalingSynthesisCandidate PhysicalMinorRecoveryCandidate
variable {n m : ℕ}

lemma same_root_potential (Y : Matrix (Fin m) (Fin m) ℝ) (x y : Fin m → ℝ)
    {C ε q : ℝ} (hw : controlledWitness Y C ε q x y)
    (hY : ∀ i j,0≤Y i j) (hmass : totalMass Y=(m:ℝ))
    (hε : 0≤ε) (hden : 0<1-q-4*ε)
    (hr : ∀ i, |ActualHessianFinite.r Y i|≤ε)
    (hc : ∀ j, |ActualHessianFinite.c Y j|≤ε) :
    let D := Real.exp (2*RawScalingSynthesis.radius C q ε)/(1-q-4*ε)
    0≤theta x y ∧ theta x y≤D*energy (ActualRootEnergy.residual Y) ∧ theta x y≤2*D*(m:ℝ)*ε^2 := by
  dsimp only
  have hroot := hw.2.2.1
  have hrow : ∀ i, ∑ j,expScaled Y x y i j=1 := hroot.1
  have hcol : ∀ j, ∑ i,expScaled Y x y i j=1 := hroot.2
  have hlo := theta_nonneg_of_exact_mass Y x y hY hrow hcol (by simpa using hmass)
  have hup := theta_upper_energy Y x y hY hmass hroot
    (Real.exp (2*RawScalingSynthesis.radius C q ε)/(1-q-4*ε)) hw.2.2.2.1
  have he := residual_energy_bound Y hε hr hc
  have hD : 0≤Real.exp (2*RawScalingSynthesis.radius C q ε)/(1-q-4*ε) :=
    div_nonneg (Real.exp_pos _).le hden.le
  refine ⟨hlo,hup,?_⟩
  have hh := mul_le_mul_of_nonneg_left he hD
  nlinarith

/-- Exact, not approximate: the signed-kappa denominator normalizes Y to mass m. -/
lemma actual_deleted_mass (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i∈Iᶜ}) (c : Fin m ≃ {j // j∈Jᶜ}) (hm : 0 < m)
    (hden : (m:ℝ)+IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J ≠ 0) :
    totalMass (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J)=(m:ℝ) := by
  have hk := physicalX_kappa T I J r c
  simp only [kappa, Fintype.card_fin] at hk
  rw [actualDeleted_eq_scalar T (complementEmbedding I r) (complementEmbedding J c) I J hm]
  simp only [totalMass, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  change (m:ℝ)/((m:ℝ)+IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J)*
    totalMass (physicalX T (complementEmbedding I r) (complementEmbedding J c))=(m:ℝ)
  have hmX : totalMass (physicalX T (complementEmbedding I r) (complementEmbedding J c))=
    (m:ℝ)+IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J := by linarith
  rw [hmX, div_mul_cancel₀ _ hden]

lemma exact_shift (T : Tournament n) (I J : Finset (Fin n)) (x y : Fin m → ℝ) :
    shiftedPotential T I J x y=theta x y+(m:ℝ)*Real.log
      ((m:ℝ)/((m:ℝ)+IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J)) := by
  exact positive_scalar_potential_transfer _ x y

lemma principal_retained_gamma (a : Fin n → ℝ) (I : Finset (Fin n)) (ha : ∀ i,|a i|<1) :
    gamma a*(∏ i∈I,(1+a i)⁻¹)*(∏ i∈I,(1-a i)⁻¹)=∏ i∈Iᶜ,(1-(a i)^2) := by
  rw [← retained_gamma a I I ha, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  ring
end SameRootPotentialCandidate
