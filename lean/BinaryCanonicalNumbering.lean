import BinaryRawGraphWeighted
import ColorTargetModels
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Canonical finite binary labels and exact ordinary tensor identification.
The identities use the existing localMatrix and doubling conventions.

The numerical vertex label is `numbering`. The enumeration supplied to the
existing `localMatrix` is `reversedNumbering`, not `numbering`: its built-in
order matrix is negative above the diagonal. Reversing that enumeration makes
the physical increasing labels have the manuscript's positive upper triangle.

`digitCount r i` counts the low r binary digits. On i < 2^r these are all the
digits of i, so `tm r i` is exactly the finite-block popcount sign.
No infinite activity sum, analytic estimate or extremal classification occurs
in this candidate. The finite identities do not assert extremal classification.
-/

noncomputable section
namespace BinaryCanonicalNumbering

open Matrix BinaryBalancedTensor

/-- Interleaved fine labels, using the existing two-layer labeling. -/
def pairFine (r : ℕ) : Fin (2^r) × Bool ≃ Fin (2^(r+1)) :=
  (ColorTransport.pairLabelEquiv (2^r)).trans
    (finCongr (by simp [pow_succ, Nat.mul_comm]))

@[simp] theorem pairFine_val (r : ℕ) (i : Fin (2^r)) (b : Bool) :
    (pairFine r (i,b)).val=ColorTransport.pairIndex i.val b := rfl

/-- Increasing numerical labels, with the newest Boolean as the low bit. -/
def numbering : (r : ℕ) → Bits r ≃ Fin (2^r)
  | 0 =>
    { toFun := fun _ => 0
      invFun := fun _ => ()
      left_inv := by intro x; cases x; rfl
      right_inv := by
        intro x
        apply Fin.ext
        have hx := x.isLt
        norm_num at hx ⊢ }
  | r+1 =>
    (Equiv.prodCongr (numbering r) (Equiv.refl Bool)).trans
      (pairFine r)

@[simp] theorem numbering_succ_val (r : ℕ) (x : Bits r) (b : Bool) :
    (numbering (r+1) (x,b)).val =
      ColorTransport.pairIndex (numbering r x).val b := rfl

/-- The enumeration needed by the existing negative-upper-triangle kernel. -/
def reversedNumbering (r : ℕ) : Bits r ≃ Fin (2^r) :=
  (numbering r).trans Fin.revPerm

theorem reversedNumbering_val (r : ℕ) (x : Bits r) :
    (reversedNumbering r x).val = 2^r-((numbering r x).val+1) := rfl

@[simp] theorem reversedNumbering_lt (r : ℕ) (x y : Bits r) :
    reversedNumbering r x < reversedNumbering r y ↔
      numbering r y < numbering r x := by
  change (numbering r x).rev < (numbering r y).rev ↔ _
  exact Fin.rev_lt_rev

/-- Number of 1 bits among the low r positions of an integer. -/
def digitCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r+1, i => digitCount r (i/2)+i%2

theorem digitCount_pair (r i : ℕ) (b : Bool) :
    digitCount (r+1) (ColorTransport.pairIndex i b) =
      digitCount r i+(if b then 1 else 0) := by
  cases b
  · have hd : (2*i)/2=i := by omega
    have hm : (2*i)%2=0 := by omega
    simp [ColorTransport.pairIndex, digitCount, hd, hm]
  · have hd : (2*i+1)/2=i := by omega
    have hm : (2*i+1)%2=1 := by omega
    simp [ColorTransport.pairIndex, digitCount, hd, hm]

/-- Explicit finite Thue--Morse/popcount sign, independent of Bits. -/
def tm (r i : ℕ) : ℝ := (-1 : ℝ)^digitCount r i

theorem tm_pair (r i : ℕ) (b : Bool) :
    tm (r+1) (ColorTransport.pairIndex i b) =
      tm r i*ColorTransport.layerSign b := by
  unfold tm
  rw [digitCount_pair]
  cases b <;> simp [ColorTransport.layerSign, pow_add]

theorem tm_sq (r i : ℕ) : tm r i^2=1 := by
  unfold tm
  rw [← pow_mul, Nat.mul_comm (digitCount r i) 2, pow_mul]
  norm_num

/-- The old recursive sign is the actual digit-count sign in increasing labels. -/
theorem sign_eq_tm (r : ℕ) (x : Bits r) :
    sign r x = (tm r (numbering r x).val : ℂ) := by
  induction r with
  | zero => cases x; simp [sign, tm, digitCount]
  | succ r ih =>
    rcases x with ⟨x,b⟩
    rw [numbering_succ_val, tm_pair]
    change sign r x*(if b then (-1 : ℂ) else 1)=
      ((tm r (numbering r x).val*ColorTransport.layerSign b : ℝ) : ℂ)
    rw [ih x]
    cases b <;> simp [ColorTransport.layerSign]

/-- The manuscript's A_r = D_t T_(2^r) D_t, extended to numerical labels.
Only labels i,j < 2^r are used for the finite block. -/
def canonicalReal (r i j : ℕ) : ℝ :=
  tm r i*tm r j*ColorTransport.orderSign i j

theorem localMatrix_order (r : ℕ) (x y : Bits r) :
    localMatrix r (reversedNumbering r) x y =
      sign r x*(ColorTransport.orderSign
        (numbering r x).val (numbering r y).val : ℂ)*sign r y := by
  unfold localMatrix ColorTransport.orderSign
  simp only [Fin.lt_def, reversedNumbering_val]
  split_ifs <;> norm_num <;> omega

/-- Exact identity, not a switching equivalence. -/
theorem localMatrix_eq_canonicalReal (r : ℕ) (x y : Bits r) :
    localMatrix r (reversedNumbering r) x y =
      (canonicalReal r (numbering r x).val (numbering r y).val : ℂ) := by
  rw [localMatrix_order, sign_eq_tm, sign_eq_tm]
  unfold canonicalReal
  push_cast
  ring

/-- The canonical local blocks obey precisely the project's existing doubling
convention J_0=[[0,-1],[1,0]], not its negative. -/
theorem canonicalReal_succ_pair (r i j : ℕ) (b c : Bool) :
    canonicalReal (r+1) (ColorTransport.pairIndex i b)
      (ColorTransport.pairIndex j c) =
      ColorTransport.doublingMatrix (canonicalReal r) i b j c := by
  unfold canonicalReal
  rw [tm_pair, tm_pair]
  have hc : tm r i^2=1 := tm_sq r i
  unfold ColorTransport.doublingMatrix
  by_cases he : i=j
  · subst j
    cases b <;> cases c <;>
      simp [ColorTransport.pairIndex, ColorTransport.layerSign,
        ColorTransport.layerJ, ColorTransport.orderSign] <;> nlinarith [hc]
  · cases b <;> cases c <;>
      simp only [ColorTransport.layerSign, ColorTransport.layerJ,
        Bool.false_eq_true, ↓reduceIte, ite_eq_right he] <;>
      unfold ColorTransport.pairIndex ColorTransport.orderSign <;>
      split_ifs <;> ring_nf <;> omega

theorem canonicalReal_depth_one (b c : Bool) :
    canonicalReal 1 (ColorTransport.pairIndex 0 b)
      (ColorTransport.pairIndex 0 c)=ColorTransport.layerJ b c := by
  rw [show 1=0+1 by omega, canonicalReal_succ_pair]
  simp [ColorTransport.doublingMatrix, canonicalReal, ColorTransport.orderSign]

/-- Independent numerical tensor formula, on ordinary coarse/fine labels. -/
def canonicalTensor {C : Type*} [DecidableEq C] (r : ℕ)
    (B : Matrix C C ℝ) : Matrix (C × Fin (2^r)) (C × Fin (2^r)) ℝ :=
  fun x y =>
    (if x.1=y.1 then canonicalReal r x.2.val y.2.val else 0)+
      B x.1 y.1*tm r x.2.val*tm r y.2.val

/-- Depth zero is the coarse graph itself, under C x Fin 1 = C. -/
theorem canonicalTensor_zero {C : Type*} [DecidableEq C]
    (B : Matrix C C ℝ) (i j : C) (a c : Fin (2^0)) :
    canonicalTensor 0 B (i,a) (j,c)=B i j := by
  simp [canonicalTensor, canonicalReal, tm, digitCount, ColorTransport.orderSign]

/-- Full tensor recursion, including the inter-coarse-block term.
Together with canonicalTensor_zero this identifies ordinary iterated doubling,
not merely the internal fine blocks. The RHS is the existing doubling formula
on the vertex type C x Fin (2^r). -/
theorem canonicalTensor_succ_pair {C : Type*} [DecidableEq C]
    (r : ℕ) (B : Matrix C C ℝ) (i j : C)
    (a c : Fin (2^r)) (b d : Bool) :
    canonicalTensor (r+1) B (i,pairFine r (a,b)) (j,pairFine r (c,d)) =
      canonicalTensor r B (i,a) (j,c)*
        ColorTransport.layerSign b*ColorTransport.layerSign d+
      (if (i,a)=(j,c) then ColorTransport.layerJ b d else 0) := by
  simp only [canonicalTensor, pairFine_val, canonicalReal_succ_pair, tm_pair,
    ColorTransport.doublingMatrix]
  by_cases hi : i=j
  · subst j
    by_cases ha : a=c
    · subst c; simp; ring
    · have hav : a.val≠c.val := fun h => ha (Fin.ext h)
      simp [ha, hav]
      ring
  · simp [hi]
    ring

theorem graph_eq_canonicalTensor {C : Type*} [DecidableEq C]
    (r : ℕ) (B : Matrix C C ℝ) (i j : C) (x y : Bits r) :
    graph r (reversedNumbering r) (ComplexifiedSkewBound.complexify B)
      (i,x) (j,y)=
      (canonicalTensor r B (i,numbering r x) (j,numbering r y) : ℂ) := by
  unfold graph BalancedTensorScores.matrix canonicalTensor
    ComplexifiedSkewBound.complexify
  simp only [localMatrix_eq_canonicalReal, sign_eq_tm]
  by_cases h : i=j <;> simp [h]

/-- Usual contiguous block labels: index = fine + 2^r * coarse. -/
def canonicalCoordinates (m r : ℕ) :
    Fin (m*2^r) ≃ Fin m × Bits r :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin m)) (numbering r).symm)

/-- This is defined from the numerical tensor formula, not from realGraph. -/
def canonicalFinGraph (m r : ℕ) (B : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (m*2^r)) (Fin (m*2^r)) ℝ :=
  fun i j => canonicalTensor r B (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)

/-- Plug e=reversedNumbering and f=canonicalCoordinates into every existing
arbitrary-enumeration bound. No raw analytic hypotheses need to be reintroduced. -/
theorem realGraph_eq_canonicalFinGraph (m r : ℕ)
    (B : Matrix (Fin m) (Fin m) ℝ) :
    BinaryRawGraphWeighted.realGraph r (reversedNumbering r) B
      (canonicalCoordinates m r)=canonicalFinGraph m r B := by
  funext i j
  let a : Fin m × Fin (2^r) := finProdFinEquiv.symm i
  let b : Fin m × Fin (2^r) := finProdFinEquiv.symm j
  change (graph r (reversedNumbering r) (ComplexifiedSkewBound.complexify B)
    (a.1,(numbering r).symm a.2) (b.1,(numbering r).symm b.2)).re =
      canonicalTensor r B a b
  rw [graph_eq_canonicalTensor]
  simp only [Equiv.apply_symm_apply, Complex.ofReal_re]

end BinaryCanonicalNumbering

#print axioms BinaryCanonicalNumbering.sign_eq_tm
#print axioms BinaryCanonicalNumbering.localMatrix_eq_canonicalReal
#print axioms BinaryCanonicalNumbering.canonicalReal_succ_pair
#print axioms BinaryCanonicalNumbering.canonicalTensor_succ_pair
#print axioms BinaryCanonicalNumbering.realGraph_eq_canonicalFinGraph
