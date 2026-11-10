import ActualReconstructionBridgeCandidate
set_option autoImplicit false
noncomputable section
namespace SameRootFrobeniusCandidate
open Matrix Finset ActualHessianFinite ActualHessianComplex MatrixScalingMassPotential
open ActualReconstructionBridgeCandidate
variable {m : ℕ}

def sqF (D : Matrix (Fin m) (Fin m) ℝ) : ℝ := ∑ i, ∑ j, D i j ^ 2

def coefficient (C ε q : ℝ) : ℝ :=
  4*C*(1+ε)*Real.exp (4*RawScalingSynthesis.radius C q ε)*
    (Real.exp (2*RawScalingSynthesis.radius C q ε)/(1-q-4*ε))^2

lemma residual_energy_bound (Y : Matrix (Fin m) (Fin m) ℝ) {ε : ℝ}
    (_hε : 0 ≤ ε) (hr : ∀ i, |r Y i| ≤ ε) (hc : ∀ j, |c Y j| ≤ ε) :
    FiniteSymmetricQuadratic.energy (ActualRootEnergy.residual Y) ≤ 2*(m:ℝ)*ε^2 := by
  have hb {z : ℝ} (hz : |z| ≤ ε) : z^2 ≤ ε^2 := by
    nlinarith [sq_abs z, (abs_le.mp hz).1, (abs_le.mp hz).2]
  unfold FiniteSymmetricQuadratic.energy ActualRootEnergy.residual
  rw [Fintype.sum_sum_type]
  have h1 : (∑ i, r Y i ^ 2) ≤ (m:ℝ)*ε^2 := by
    calc
      _ ≤ ∑ _i : Fin m, ε^2 := sum_le_sum (fun i _ => hb (hr i))
      _ = _ := by simp
  have h2 : (∑ j, c Y j ^ 2) ≤ (m:ℝ)*ε^2 := by
    calc
      _ ≤ ∑ _j : Fin m, ε^2 := sum_le_sum (fun j _ => hb (hc j))
      _ = _ := by simp
  simpa only [Sum.elim_inl, Sum.elim_inr] using (show
    (∑ i, r Y i ^ 2)+(∑ j, c Y j ^ 2) ≤ 2*(m:ℝ)*ε^2 by linarith)

/-- Every estimate is for the supplied witness, never a new chosen root. -/
lemma same_root_squared_bound (hm : 0 < m) (Y : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m → ℝ) {C ε q : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hw : controlledWitness Y C ε q x y)
    (hr : ∀ i, |r Y i| ≤ ε) (hc : ∀ j, |c Y j| ≤ ε) :
    sqF (expScaled Y x y-Y) ≤ coefficient C ε q * ε^2 := by
  have hE := residual_energy_bound Y hε hr hc
  have hF := hw.2.2.2.2.2.1
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  let a := RawScalingSynthesis.radius C q ε
  have hp : 0 ≤ (2*C*(1+ε)*Real.exp (4*a)/(m:ℝ))*(Real.exp (2*a)/(1-q-4*ε))^2 := by positivity
  change sqF (expScaled Y x y-Y) ≤ _ at hF
  apply hF.trans
  calc
    _ ≤ (2*C*(1+ε)*Real.exp (4*a)/(m:ℝ))*(Real.exp (2*a)/(1-q-4*ε))^2*(2*(m:ℝ)*ε^2) :=
      mul_le_mul_of_nonneg_left hE hp
    _ = coefficient C ε q * ε^2 := by unfold coefficient; dsimp [a]; field_simp; ring

lemma same_root_centering (hm : 0 < m) (Y : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m → ℝ) {C ε q : ℝ} (hw : controlledWitness Y C ε q x y) :
    expScaled Y x y-P m-(1-P m)*Y*(1-P m) =
      (1-P m)*(expScaled Y x y-Y)*(1-P m) := by
  have hroot := hw.2.2.1
  have hh := ScalingCenteredGap.centered_decomposition hm Y (expScaled Y x y)
    (by simpa [expScaled] using hroot.1) (by simpa [expScaled] using hroot.2)
  rw [hh]; abel

lemma sqrt_squared_bound (D : Matrix (Fin m) (Fin m) ℝ) {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hD : sqF D ≤ K*ε^2) :
    Real.sqrt (sqF D) ≤ Real.sqrt K*ε := by
  calc
    _ ≤ Real.sqrt (K*ε^2) := Real.sqrt_le_sqrt hD
    _ = _ := by rw [Real.sqrt_mul hK, Real.sqrt_sq hε]

/-- Uniform constant once C, radius, epsilon and the coercivity denominator
are bounded on a fixed logarithmic window. No dimension factor remains. -/
lemma coefficient_uniform {C ε q Cstar estar astar d : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hd : 0 < d)
    (hCs : C ≤ Cstar) (hεs : ε ≤ estar)
    (ha : RawScalingSynthesis.radius C q ε ≤ astar)
    (hden : d ≤ 1-q-4*ε) :
    coefficient C ε q ≤ 4*Cstar*(1+estar)*Real.exp (4*astar)*
      (Real.exp (2*astar)/d)^2 := by
  unfold coefficient
  have hdenpos : 0 < 1-q-4*ε := hd.trans_le hden
  have hCs0 := hC.trans hCs
  have hεs0 := hε.trans hεs
  gcongr

lemma left_sqF_contraction (Q D : Matrix (Fin m) (Fin m) ℝ)
    (hQ : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Q‖ ≤ 1) :
    sqF (Q*D) ≤ sqF D := by
  have hv (v : Fin m → ℝ) :
      FiniteSymmetricQuadratic.energy (Q *ᵥ v) ≤ FiniteSymmetricQuadratic.energy v := by
    have hh := (Matrix.toEuclideanCLM (𝕜 := ℝ) Q).le_opNorm
      (WithLp.toLp 2 v)
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
    change ‖(WithLp.toLp 2 (Q *ᵥ v) : EuclideanSpace ℝ (Fin m))‖ ≤
      1*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))‖ at hh'
    rw [FiniteSymmetricQuadratic.norm_eq_l2, FiniteSymmetricQuadratic.norm_eq_l2,
      one_mul] at hh'
    unfold FiniteSymmetricQuadratic.l2 at hh'
    exact (Real.sqrt_le_sqrt_iff (FiniteSymmetricQuadratic.energy_nonneg v)).mp hh'
  unfold sqF
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => D i j ^ 2)]
  apply Finset.sum_le_sum
  intro j _
  simpa [FiniteSymmetricQuadratic.energy, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    using hv (fun i => D i j)

lemma sqF_transpose (D : Matrix (Fin m) (Fin m) ℝ) : sqF D.transpose = sqF D := by
  unfold sqF
  exact Finset.sum_comm

lemma centered_sqF_contraction (hm : 0 < m) (D : Matrix (Fin m) (Fin m) ℝ) :
    sqF ((1-P m)*D*(1-P m)) ≤ sqF D := by
  have hp : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin m) (1-P m)‖ ≤ 1 :=
    RawScalingSynthesis.real_gap_of_complex _ (by norm_num)
      (ScalingCenteredGap.projection_data hm).2.2
  have ht : (1-P m : Matrix (Fin m) (Fin m) ℝ).transpose = 1-P m := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.one_apply, P, eq_comm]
  have hright : sqF (D*(1-P m)) ≤ sqF D := by
    rw [← sqF_transpose (D*(1-P m)), Matrix.transpose_mul, ht]
    exact (left_sqF_contraction _ _ hp).trans_eq (sqF_transpose D)
  rw [Matrix.mul_assoc]
  exact (left_sqF_contraction _ _ hp).trans hright

end SameRootFrobeniusCandidate
