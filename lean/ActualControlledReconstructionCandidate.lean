import ActualKappaBridgeCandidate
import LogWindowDeletionBudgetCandidate
set_option autoImplicit false
noncomputable section
namespace ActualControlledReconstructionCandidate
open Matrix Finset Filter TournamentHamiltonian ActualTournamentPrescalingBounds
open MatrixScalingMassPotential NonprincipalReconstructionCandidate
open ActualReconstructionBridgeCandidate ActualKappaBridgeCandidate
open ActualPrescalingNormalization DeletedScalingSynthesisCandidate
open ActualNormalizedCenteredGapCandidate TournamentPrescalingMassBound
open scoped Topology
variable {n m : ℕ}

lemma complement_image (I : Finset (Fin n)) (r : Fin m ≃ {i // i ∈ Iᶜ}) :
    univ.image (complementEmbedding I r)=Iᶜ := by
  ext i
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨j,rfl⟩
    exact (r j).property
  · intro hi
    refine ⟨r.symm ⟨i,hi⟩,?_⟩
    change (r (r.symm ⟨i,hi⟩)).val=i
    simp
lemma complement_card_eq (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ}) : J.card=I.card := by
  have hr := complement_card I r
  have hc := complement_card J c
  have hh : (J.card:ℝ)=(I.card:ℝ) := by linarith
  exact_mod_cast hh

def reconstructedWitness (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (C ε q : ℝ) (x y : Fin m → ℝ) : Prop :=
  let e := complementEmbedding I r
  let f := complementEmbedding J c
  let Y := actualDeleted T e f I J
  let X := physicalX T e f
  let k := IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J
  let s := (m:ℝ)/((m:ℝ)+k)
  let xx := fun i => x i+Real.log s/2
  let yy := fun j => y j+Real.log s/2
  controlledWitness Y C ε q x y ∧
  expScaled X xx yy=expScaled Y x y ∧
  ActualRootEnergy.root X xx yy ∧
  (∑ i,xx i)=(∑ j,yy j) ∧
  -theta xx yy≤k ∧
  ((ActualReconstructionBridgeCandidate.adjacency T).submatrix e f).permanent =
    gamma (normalizedScore T)*(∏ i ∈ I,(1+normalizedScore T i)⁻¹)*
      (∏ j ∈ J,(1-normalizedScore T j)⁻¹)*
      ((m:ℝ)*((n:ℝ)-1)*((n:ℝ)+ActualPrescalingNormalization.nu T)/(2*(n:ℝ)^2))^m*
      Real.exp (-theta xx yy)*(expScaled Y x y).permanent

lemma combine_same_root (T : Tournament n) (I J : Finset (Fin n))
    (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (hn : 2≤n) (hm : 0 < m) {a0 : ℝ} (h0 : 0≤a0) (h1 : a0<1)
    (ha : ∀ i,|normalizedScore T i|≤a0)
    (hk : 0<(m:ℝ)+IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J)
    (C ε q : ℝ) (hctrl : controlled
      (actualDeleted T (complementEmbedding I r) (complementEmbedding J c) I J) C ε q) :
    ∃ x y, reconstructedWitness T I J r c C ε q x y := by
  obtain ⟨x,y,hw,hr,heq,hroot,hgauge,hθ⟩ := controlled_actual_root_transfer T
    (complementEmbedding I r) (complementEmbedding J c) I J hm hk C ε q hctrl
    (physicalX_nonnegative T _ _ hn h0 h1 ha)
  refine ⟨x,y,hw,heq,hroot,hgauge,?_,?_⟩
  · simpa only [physicalX_kappa] using hθ
  · have hh := actual_permanent_reconstruction T I J r c hn hm h0 h1 ha
      (fun i => x i+Real.log ((m:ℝ)/((m:ℝ)+IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J))/2)
      (fun j => y j+Real.log ((m:ℝ)/((m:ℝ)+IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J))/2)
    change _ = _ * (expScaled (physicalX T (complementEmbedding I r) (complementEmbedding J c)) _ _).permanent at hh
    rw [heq] at hh
    exact hh

lemma actual_denominator_positive (T : Tournament n) (I J : Finset (Fin n))
    (hn : 2≤n) {a0 : ℝ} (h0 : 0≤a0) (h1 : a0<1)
    (ha : ∀ i,|normalizedScore T i|≤a0) (hcard : J.card=I.card) (hhalf : 2*I.card≤n)
    (hsmall : actualK T a0 I < (m:ℝ)) :
    0<(m:ℝ)+IndependentDeletionMass.deletionExcess (normalizedMatrix T) I J := by
  have hk := actual_independent_deletion_bound T hn h0 h1 ha I J hcard hhalf
  change abs _ ≤ actualK T a0 I at hk
  have hh := (abs_le.mp hk).1
  linarith

-- No target root, nonnegativity or denominator hypothesis remains in this endpoint.
theorem actual_controlled_reconstruction (T : Tournament n) (hn : 24≤n) (hm : 0 < m)
    (I J : Finset (Fin n)) (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ})
    (hhalf : 2*I.card≤n) {a0 : ℝ} (h0 : 0≤a0) (h1 : a0<1)
    (ha : ∀ i,|normalizedScore T i|≤a0)
    (herr : Real.sqrt (errorBudget T a0)≤1/46)
    (hsmall : actualK T a0 I < (m:ℝ))
    (hgap : gapBudget n m (39/46) (actualK T a0 I)<1)
    (hthreshold : residualBudget n m I.card (16*(scaleCap a0)^2)
      (normalizedMarginalBound T a0) (actualK T a0 I) ≤
      RawScalingSynthesis.epsilonThreshold (density m (16*(scaleCap a0)^2) (actualK T a0 I))
        (gapBudget n m (39/46) (actualK T a0 I))) :
    ∃ x y, reconstructedWitness T I J r c
      (density m (16*(scaleCap a0)^2) (actualK T a0 I))
      (residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I))
      (gapBudget n m (39/46) (actualK T a0 I)) x y := by
  have hcard := complement_card_eq I J r c
  apply combine_same_root T I J r c (by omega) hm h0 h1 ha
    (actual_denominator_positive T I J (by omega) h0 h1 ha hcard hhalf hsmall)
  exact actual_deleted_scaling T hn hm (complementEmbedding I r) (complementEmbedding J c) I J
    (complement_image I r) (complement_image J c) hcard hhalf (complement_card I r)
    h0 h1 ha herr hsmall hgap hthreshold
open LogWindowDeletionBudgetCandidate LogWindowErrorCandidate
 theorem eventually_actual_reconstruction {A B a0 : ℝ}
    (hA : 0≤A) (hB : 0≤B) (h0 : 0≤a0) (h1 : a0<1) :
    ∀ᶠ n : ℕ in atTop, ∀ (T : Tournament n) (m : ℕ) (I J : Finset (Fin n))
      (r : Fin m ≃ {i // i ∈ Iᶜ}) (c : Fin m ≃ {j // j ∈ Jᶜ}),
      (∀ i,|normalizedScore T i|≤a0) →
      tau (normalizedScore T)≤A*Real.log (n:ℝ) →
      (I.card:ℝ)≤B*Real.log (n:ℝ) →
      ∃ x y, reconstructedWitness T I J r c
        (density m (16*(scaleCap a0)^2) (actualK T a0 I))
        (residualBudget n m I.card (16*(scaleCap a0)^2) (normalizedMarginalBound T a0) (actualK T a0 I))
        (gapBudget n m (39/46) (actualK T a0 I)) x y := by
  filter_upwards [eventually_ge_atTop 24, eventually_actual_error_small A a0,
    eventually_remaining_budgets (a0:=a0) hA hB,
    (deletionRatio_tendsto B).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
    with n hn herr hbud hratio
  intro T m I J r c ha hτ ht
  have hm := complement_card I r
  have hbudget := hbud T I m hm hτ ht
  have hk0 : 0≤actualK T a0 I := by
    have hd0 := normalizedMarginalBound_nonneg T a0
    unfold actualK
    positivity
  have hm0 : 0 < m := by exact_mod_cast (lt_of_le_of_lt hk0 hbudget.1)
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have htRatio : (I.card:ℝ)/(n:ℝ)≤1/2 :=
    (div_le_div_of_nonneg_right ht hnR.le).trans hratio.le
  have htHalf : (2:ℝ)*(I.card:ℝ)≤(n:ℝ) := by
    have hh := (div_le_iff₀ hnR).mp htRatio
    linarith
  have hhalf : 2*I.card≤n := by exact_mod_cast htHalf
  exact actual_controlled_reconstruction T hn hm0 I J r c hhalf h0 h1 ha
    (herr T hτ) hbudget.1 hbudget.2.1 hbudget.2.2
end ActualControlledReconstructionCandidate

#print axioms ActualControlledReconstructionCandidate.complement_image
#check ActualControlledReconstructionCandidate.complement_image

#print axioms ActualControlledReconstructionCandidate.complement_card_eq
#check ActualControlledReconstructionCandidate.complement_card_eq

#print axioms ActualControlledReconstructionCandidate.reconstructedWitness
#check ActualControlledReconstructionCandidate.reconstructedWitness

#print axioms ActualControlledReconstructionCandidate.combine_same_root
#check ActualControlledReconstructionCandidate.combine_same_root

#print axioms ActualControlledReconstructionCandidate.actual_denominator_positive
#check ActualControlledReconstructionCandidate.actual_denominator_positive

#print axioms ActualControlledReconstructionCandidate.actual_controlled_reconstruction
#check ActualControlledReconstructionCandidate.actual_controlled_reconstruction

#print axioms ActualControlledReconstructionCandidate.eventually_actual_reconstruction
#check ActualControlledReconstructionCandidate.eventually_actual_reconstruction
