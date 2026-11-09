import RawPhysicalWeightedNorm
import PartialMatchingWeightedBound

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace RawActivityLabelNorm
open StructuralPartialMatchingCounts PartialMatchingAffine WeightedCoefficientNorm

def covarianceBound (n : ℕ) (rho s q C : ℝ) :=
  ((s*C+2*s^2*C^2/(1-s*q))/(n:ℝ))/(1-rho/s)
def meanBound (n : ℕ) (rho s q C K : ℝ) :=
  ((s*K+2*s^2*C*K/(1-s*q))/(n:ℝ))/(1-rho/s)

theorem label_bound {n : ℕ} (hn : 0<n)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (hQ : ∀i j,Q i j=Q j i)
    {rho s q C K : ℝ} (hr : 0 ≤ rho) (hrs : rho<s) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hq : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) Q‖ ≤ q) (hgap : s*q<1)
    (hentry : ∀i j,‖Q i j‖ ≤ C/(n:ℝ))
    (hscore : ∀i,‖(Q.mulVec (fun _ => 1)) i‖ ≤ K/(n:ℝ))
    {b : ℕ} (d : Fin b → ℕ) (p : PartialPairing (Positions d)) :
    (∑a : Fin b → (Fin n ⊕ Fin n),norm rho
      (weight (PhysicalTiltedCovariance.covariance Q RawFormalMixedSpecialization.identityInteraction)
        (PhysicalPartialMatching.covariance_symmetry Q _ hQ
          (fun i j => by simp [RawFormalMixedSpecialization.identityInteraction,Matrix.one_apply,eq_comm]))
        (PhysicalTiltedCovariance.mean Q RawFormalMixedSpecialization.identityInteraction (fun _ => 1))
        (fun x : Positions d => a x.1) p)) ≤
      (2*(n:ℝ))^b*(covarianceBound n rho s q C ^pairCount p * meanBound n rho s q C K ^singletonCount p) := by
  have hh := RawPhysicalWeightedNorm.bounds hn Q hr hrs hC hK hq hgap hentry hscore
  have hs : 0<s := hr.trans_lt hrs
  have hden : 0<1-rho/s := by have := (div_lt_one hs).mpr hrs; linarith
  have hgap' : 0<1-s*q := by linarith
  have hB : 0 ≤ covarianceBound n rho s q C := by unfold covarianceBound; positivity
  have hE : 0 ≤ meanBound n rho s q C K := by unfold meanBound; positivity
  have hx := PartialMatchingWeightedBound.labels d p
    (PhysicalTiltedCovariance.covariance Q RawFormalMixedSpecialization.identityInteraction)
    (PhysicalPartialMatching.covariance_symmetry Q _ hQ
      (fun i j => by simp [RawFormalMixedSpecialization.identityInteraction,Matrix.one_apply,eq_comm]))
    (PhysicalTiltedCovariance.mean Q RawFormalMixedSpecialization.identityInteraction (fun _ => 1))
    hr hB hE (fun i j => (hh.1 i j).1) (fun i => (hh.2 i).1)
    (fun i j => (hh.1 i j).2) (fun i => (hh.2 i).2)
  simpa only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,two_mul] using hx
end RawActivityLabelNorm
#print axioms RawActivityLabelNorm.label_bound
