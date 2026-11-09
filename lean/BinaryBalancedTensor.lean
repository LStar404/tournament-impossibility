import BalancedTensorScores
noncomputable section
namespace BinaryBalancedTensor
open Matrix

def Bits : ℕ → Type
  | 0 => Unit
  | r+1 => Bits r × Bool
instance (r : ℕ) : Fintype (Bits r) := by
  induction r with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ r ih => exact inferInstanceAs (Fintype (Bits r × Bool))
instance (r : ℕ) : DecidableEq (Bits r) := Classical.typeDecidableEq _
def sign : (r : ℕ) → Bits r → ℂ
  | 0, _ => 1
  | r+1, x => sign r x.1 * (if x.2 then -1 else 1)

theorem card (r : ℕ) : Fintype.card (Bits r)=2^r := by
  induction r with
  | zero => rfl
  | succ r ih => change Fintype.card (Bits r × Bool)=_; simp [ih,pow_succ]

theorem sign_norm (r : ℕ) (x : Bits r) : ‖sign r x‖=1 := by
  induction r with
  | zero => simp [sign]
  | succ r ih => change ‖sign r x.1*(if x.2 then -1 else 1)‖=1
                 rw [norm_mul,ih]; cases x.2 <;> norm_num

theorem balanced (r : ℕ) : (∑x:Bits (r+1),sign (r+1) x)=0 := by
  change (∑x:Bits r × Bool, sign r x.1*(if x.2 then -1 else 1))=0
  simp [Fintype.sum_prod_type,Fintype.sum_bool]

def localMatrix (r : ℕ) (e : Bits r ≃ Fin (2^r)) : Matrix (Bits r) (Bits r) ℂ :=
  fun x y => sign r x*(if e x<e y then -1 else if e y<e x then 1 else 0)*sign r y

theorem local_entry (r : ℕ) (e : Bits r ≃ Fin (2^r)) (x y : Bits r) :
    ‖localMatrix r e x y‖ ≤ 1 := by
  simp only [localMatrix,norm_mul,sign_norm,one_mul,mul_one]
  split_ifs <;> norm_num

def graph {C : Type*} [DecidableEq C] (r : ℕ) (e : Bits r ≃ Fin (2^r))
    (B : Matrix C C ℂ) := BalancedTensorScores.matrix (localMatrix r e) B (sign r)

theorem branch_scores {C : Type*} [Fintype C] [DecidableEq C]
    (r : ℕ) (e : Bits (r+1) ≃ Fin (2^(r+1))) (B : Matrix C C ℂ)
    (v : ℂ) (n : ℕ) (hn : 0<n) (x : C × Bits (r+1)) :
    ‖(((n:ℂ)⁻¹ • (graph (r+1) e B+v • (1:Matrix _ _ ℂ))).mulVec (fun _ => 1) x)‖ ≤
      ((2:ℝ)^(r+1)+‖v‖)/(n:ℝ) := by
  have h := BalancedTensorScores.branch_score (localMatrix (r+1) e) B (sign (r+1))
    (balanced r) v n hn (local_entry (r+1) e) x
  simpa only [graph,card,Nat.cast_pow,Nat.cast_ofNat,mul_one] using h
theorem branch_column_scores {C : Type*} [Fintype C] [DecidableEq C]
    (r : ℕ) (e : Bits (r+1) ≃ Fin (2^(r+1))) (B : Matrix C C ℂ)
    (v : ℂ) (n : ℕ) (hn : 0<n) (x : C × Bits (r+1)) :
    ‖((((n:ℂ)⁻¹ • (graph (r+1) e B+v • (1:Matrix _ _ ℂ))).transpose).mulVec (fun _ => 1) x)‖ ≤
      ((2:ℝ)^(r+1)+‖v‖)/(n:ℝ) := by
  have h := BalancedTensorScores.branch_column_score (localMatrix (r+1) e) B (sign (r+1))
    (balanced r) v n hn (local_entry (r+1) e) x
  simpa only [graph,card,Nat.cast_pow,Nat.cast_ofNat,mul_one] using h

end BinaryBalancedTensor
#print axioms BinaryBalancedTensor.branch_scores
