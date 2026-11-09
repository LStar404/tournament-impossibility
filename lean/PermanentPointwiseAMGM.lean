import PermanentFactorEnergy
import PermanentPolarization
import Mathlib.Analysis.MeanInequalities
noncomputable section
namespace PermanentPositiveMoments
open Matrix
lemma prod_le_mean_pow {n : ℕ} (hn : 0<n) (f : Fin n → ℝ) (hf : ∀i,0≤f i) :
    (∏i, f i) ≤ ((∑i,f i)/(n:ℝ))^n := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin n => (n:ℝ)⁻¹) f (fun _ _ => inv_nonneg.mpr hnR.le)
    (by simp [ne_of_gt hnR]) (fun i _ => hf i)
  have hp := pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hf i) _)) h n
  have he : (∏ i, (f i)^((n:ℝ)⁻¹))^n = ∏i, f i := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Real.rpow_mul_natCast (hf i), inv_mul_cancel₀ (ne_of_gt hnR), Real.rpow_one]
  rw [he] at hp
  simpa only [← Finset.mul_sum, inv_mul_eq_div, ← Finset.sum_div] using hp

lemma complex_product_bound {n : ℕ} (hn : 0<n) (x y : Fin n → ℂ) (E : ℝ)
    (hx : ∑i, ‖x i‖^2=E) (hy : ∑i, ‖y i‖^2=E) :
    ‖(∏i,x i)*star (∏i,y i)‖ ≤ (E/(n:ℝ))^n := by
  have hE : 0≤E := hx ▸ Finset.sum_nonneg (fun i _ => sq_nonneg ‖x i‖)
  have h1 := prod_le_mean_pow hn (fun i => ‖x i‖^2) (fun i => sq_nonneg _)
  have h2 := prod_le_mean_pow hn (fun i => ‖y i‖^2) (fun i => sq_nonneg _)
  rw [hx, Finset.prod_pow] at h1
  rw [hy, Finset.prod_pow] at h2
  have hm := mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
  simp only [norm_mul, norm_star, norm_prod]
  have hp : 0 ≤ (∏i, ‖x i‖)*(∏i, ‖y i‖) := by positivity
  have hq : 0 ≤ (E/(n:ℝ))^n := by positivity
  nlinarith [sq_nonneg ((∏i, ‖x i‖)*(∏i, ‖y i‖) - (E/(n:ℝ))^n)]

/-- A pointwise bound for the actual constructed factors; integration remains a separate step. -/
theorem actual_pointwise {n : ℕ} (hn : 0<n) (A : Matrix (Fin n) (Fin n) ℂ)
    (g : Fin n → ℂ) :
    ‖(∏i,(PermanentSpectralFrame.leftFactor A*ᵥg) i) *
      star (∏i,(PermanentSpectralFrame.rightFactor A*ᵥg) i)‖ ≤
    ((∑i, PermanentSpectralFrame.singularRoot A i * ‖g i‖^2)/(n:ℝ))^n :=
  complex_product_bound hn _ _ _
    (PermanentSpectralFrame.actual_factor_energy A g)
    (PermanentSpectralFrame.actual_right_energy A g)
end PermanentPositiveMoments
#print axioms PermanentPositiveMoments.actual_pointwise
