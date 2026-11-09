import BinaryBalancedTensor
import TournamentRawWeighted
noncomputable section
namespace BinaryGraphTransport
open Matrix BinaryBalancedTensor

theorem sign_im (r : ℕ) (x : Bits r) : (sign r x).im=0 := by
  induction r with
  | zero => simp [sign]
  | succ r ih =>
      change (sign r x.1*(if x.2 then -1 else 1)).im=0
      split_ifs <;> simp [Complex.mul_im,ih]

theorem sign_real (r : ℕ) (x : Bits r) : ((sign r x).re:ℂ)=sign r x := by
  apply Complex.ext <;> simp [sign_im]

theorem local_im (r : ℕ) (e : Bits r ≃ Fin (2^r)) (x y : Bits r) :
    (localMatrix r e x y).im=0 := by
  unfold localMatrix
  split_ifs <;> simp [Complex.mul_im,sign_im]

theorem local_real (r : ℕ) (e : Bits r ≃ Fin (2^r)) (x y : Bits r) :
    ((localMatrix r e x y).re:ℂ)=localMatrix r e x y := by
  apply Complex.ext <;> simp [local_im]

theorem local_skew (r : ℕ) (e : Bits r ≃ Fin (2^r)) (x y : Bits r) :
    localMatrix r e y x= -localMatrix r e x y := by
  unfold localMatrix
  by_cases h : e x<e y
  · have h' : ¬e y<e x := not_lt_of_ge h.le
    simp [h,h']; ring
  · by_cases h' : e y<e x
    · simp [h,h']; ring
    · simp [h,h']

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem graph_real (r : ℕ) (e : Bits r ≃ Fin (2^r)) (B : Matrix C C ℝ)
    (x y : C × Bits r) :
    ((graph r e (ComplexifiedSkewBound.complexify B) x y).re:ℂ)=
      graph r e (ComplexifiedSkewBound.complexify B) x y := by
  apply Complex.ext
  · simp
  · unfold graph BalancedTensorScores.matrix ComplexifiedSkewBound.complexify
    split_ifs <;> simp [Complex.mul_im,sign_im,local_im]

theorem graph_skew (r : ℕ) (e : Bits r ≃ Fin (2^r)) (B : Matrix C C ℝ)
    (hB : ∀ i j,B j i= -B i j) (x y : C × Bits r) :
    graph r e (ComplexifiedSkewBound.complexify B) y x =
      -graph r e (ComplexifiedSkewBound.complexify B) x y := by
  unfold graph BalancedTensorScores.matrix ComplexifiedSkewBound.complexify
  rw [hB x.1 y.1,Complex.ofReal_neg,local_skew]
  by_cases h : x.1=y.1 <;> simp [h,eq_comm] <;> ring

theorem graph_entry (r : ℕ) (e : Bits r ≃ Fin (2^r)) (B : Matrix C C ℝ)
    (hB : ∀ i j,B j i= -B i j) (he : ∀ i j,|B i j| ≤ 1)
    (x y : C × Bits r) :
    ‖graph r e (ComplexifiedSkewBound.complexify B) x y‖ ≤ 1 := by
  unfold graph BalancedTensorScores.matrix ComplexifiedSkewBound.complexify
  by_cases h : x.1=y.1
  · have hd : B y.1 y.1=0 := by have hh := hB y.1 y.1; linarith
    simp only [h,ite_true,hd,Complex.ofReal_zero,zero_mul,add_zero]
    exact local_entry r e x.2 y.2
  · simp only [h,ite_false,zero_add,norm_mul,sign_norm,mul_one,Complex.norm_real,Real.norm_eq_abs]
    exact he x.1 y.1
end BinaryGraphTransport
#print axioms BinaryGraphTransport.graph_entry
