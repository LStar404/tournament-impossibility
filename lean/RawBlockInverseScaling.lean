import RawResolventMeanBound

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace RawBlockInverseScaling
open Matrix WithLp

theorem bounds {n : ℕ} (hn : 0<n)
    (Q R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (z : ℂ)
    (hR : R*(1+z • Q)=1) {s C K L : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hs : ‖z‖ ≤ s)
    (hq : ∀i j,‖Q i j‖ ≤ C/(n:ℝ))
    (hb : ∀i,‖(Q.mulVec (fun _ => 1)) i‖ ≤ K/(n:ℝ))
    (hL : ‖Matrix.toEuclideanCLM (𝕜:=ℂ) R‖ ≤ L) :
    (∀i j,‖((z • Q)*R) i j‖ ≤ (s*C+2*s^2*C^2*L)/(n:ℝ)) ∧
    (∀i,‖(((z • Q)*R).mulVec (fun _ => 1)) i‖ ≤ (s*K+2*s^2*C*L*K)/(n:ℝ)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hc : (Fintype.card (Fin n ⊕ Fin n):ℝ)=2*(n:ℝ) := by simp; ring
  have hu (i : Fin n ⊕ Fin n) : ‖toLp 2 (fun a => Q i a)‖ ≤ Real.sqrt (2*(n:ℝ))*(C/(n:ℝ)) := by
    simpa only [hc] using RawResolventMeanBound.vector_bound (fun a => Q i a)
      (div_nonneg hC hnR.le) (hq i)
  have hv (j : Fin n ⊕ Fin n) : ‖toLp 2 (fun a => Q a j)‖ ≤ Real.sqrt (2*(n:ℝ))*(C/(n:ℝ)) := by
    simpa only [hc] using RawResolventMeanBound.vector_bound (fun a => Q a j)
      (div_nonneg hC hnR.le) (fun i => hq i j)
  have hb2 : ‖toLp 2 (Q.mulVec (fun _ => 1))‖ ≤ Real.sqrt (2*(n:ℝ))*(K/(n:ℝ)) := by
    simpa only [hc] using RawResolventMeanBound.vector_bound _ (div_nonneg hK hnR.le) hb
  have hsqrt : (Real.sqrt (2*(n:ℝ)))^2=2*(n:ℝ) := Real.sq_sqrt (by positivity)
  constructor
  · intro i j
    have hh := RawResolventEntryBound.entry Q R z hR i j hs (hq i j) (hu i) (hv j) hL
    convert hh using 1
    rw [mul_pow,hsqrt]
    field_simp
    <;> ring
  · intro i
    have hh := RawResolventMeanBound.mean Q R z hR i hs (hb i) (hu i) hb2 hL
    convert hh using 1
    have he : s^2*(Real.sqrt (2*(n:ℝ))*(C/(n:ℝ)))*L*
        (Real.sqrt (2*(n:ℝ))*(K/(n:ℝ)))=2*s^2*C*L*K/(n:ℝ) := by
      calc
        _ = s^2*(Real.sqrt (2*(n:ℝ)))^2*C*L*K/(n:ℝ)^2 := by ring
        _ = _ := by rw [hsqrt]; field_simp
    rw [he]
    ring
end RawBlockInverseScaling
#print axioms RawBlockInverseScaling.bounds
