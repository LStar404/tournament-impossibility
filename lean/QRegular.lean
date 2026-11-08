import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Analysis.Complex.Basic

/-! The standard finite-dimensional q-kernel definition, and its zero-digit orbit. -/
open Matrix
open scoped BigOperators
namespace NonAlgebraicity

 def qKernel (q : ℕ) (a : ℕ → ℂ) : Set (ℕ → ℂ) :=
  {f | ∃ e r : ℕ, r < q ^ e ∧ f = fun n => a (q ^ e * n + r)}

 def qKernelSpace (q : ℕ) (a : ℕ → ℂ) : Submodule ℂ (ℕ → ℂ) :=
  Submodule.span ℂ (qKernel q a)

 def IsQRegular (q : ℕ) (a : ℕ → ℂ) : Prop :=
  FiniteDimensional ℂ (qKernelSpace q a)

 def zeroDigit (q : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f n := f (q * n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem self_mem_qKernel (q : ℕ) (a : ℕ → ℂ) : a ∈ qKernel q a := by
  refine ⟨0, 0, by simp, ?_⟩
  simp

 theorem zeroDigit_mem (q : ℕ) (hq : 2 ≤ q) (a f : ℕ → ℂ)
    (hf : f ∈ qKernelSpace q a) : zeroDigit q f ∈ qKernelSpace q a := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨e, r, hr, rfl⟩ := hf
    apply Submodule.subset_span
    refine ⟨e + 1, r, lt_of_lt_of_le hr ?_, ?_⟩
    · rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ (by omega)
    · ext n
      simp [zeroDigit, pow_succ, Nat.mul_assoc]
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa using (qKernelSpace q a).add_mem ihx ihy
  | smul c x hx ih =>
    simpa using (qKernelSpace q a).smul_mem c ih

 def kernelZeroDigit (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℂ) :
    qKernelSpace q a →ₗ[ℂ] qKernelSpace q a :=
  (zeroDigit q).restrict (zeroDigit_mem q hq a)

 def kernelInitial (q : ℕ) (a : ℕ → ℂ) : qKernelSpace q a :=
  ⟨a, Submodule.subset_span (self_mem_qKernel q a)⟩

 theorem kernelZeroDigit_pow (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℂ) (e n : ℕ) :
    ((kernelZeroDigit q hq a ^ e) (kernelInitial q a) : ℕ → ℂ) n = a (q ^ e * n) := by
  induction e generalizing n with
  | zero => simp [kernelInitial]
  | succ e ih =>
    rw [pow_succ']
    change ((kernelZeroDigit q hq a ^ e) (kernelInitial q a) : ℕ → ℂ) (q * n) = _
    rw [ih]
    simp [pow_succ, Nat.mul_assoc]

/-- A standard q-regular sequence has a finite matrix representation along powers of q. -/
 theorem qRegular_power_representation (q : ℕ) (hq : 2 ≤ q) (a : ℕ → ℂ)
    (ha : IsQRegular q a) :
    ∃ d : ℕ, ∃ M : Matrix (Fin d) (Fin d) ℂ, ∃ v l : Fin d → ℂ,
      ∀ e, a (q ^ e) = l ⬝ᵥ ((M ^ e) *ᵥ v) := by
  classical
  let : FiniteDimensional ℂ (qKernelSpace q a) := ha
  let b := Module.finBasis ℂ (qKernelSpace q a)
  let T := kernelZeroDigit q hq a
  let x := kernelInitial q a
  let ev : qKernelSpace q a →ₗ[ℂ] ℂ :=
    { toFun := fun f => (f : ℕ → ℂ) 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨_, LinearMap.toMatrix b b T, b.repr x, fun i => ev (b i), ?_⟩
  intro e
  rw [LinearMap.toMatrix_pow, LinearMap.toMatrix_mulVec_repr]
  have he : ev ((T ^ e) x) = a (q ^ e) := by
    simpa [ev, T, x] using kernelZeroDigit_pow q hq a e 1
  rw [← he]
  conv_lhs => rw [← b.sum_repr ((T ^ e) x)]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

end NonAlgebraicity

#print axioms NonAlgebraicity.qRegular_power_representation
