import ColorGraphRepair
namespace ColorTransport

/-- Independent two-layer doubling convention from the manuscript:
I⊗J₀+B⊗ttᵀ, with t=(1,-1), J₀=[[0,-1],[1,0]]. -/
def layerSign (r : Bool) : ℝ := if r then -1 else 1

def layerJ (r s : Bool) : ℝ := if r=s then 0 else if r then 1 else -1

def doublingMatrix (B : ℕ → ℕ → ℝ) (i : ℕ) (r : Bool) (j : ℕ) (s : Bool) : ℝ :=
  B i j * layerSign r * layerSign s + if i=j then layerJ r s else 0

def pairIndex (i : ℕ) (r : Bool) : ℕ := 2*i + if r then 1 else 0

private theorem paired_get_even (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (paired w).getD (2*i) false = w.getD i false := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero => simp [paired]
    | succ i =>
      have he : 2*(i+1) = (2*i+1)+1 := by omega
      simpa [paired, he] using ih i (by simpa using hi)

private theorem paired_get_odd (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (paired w).getD (2*i+1) false = !(w.getD i false) := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero => simp [paired]
    | succ i =>
      have he : 2*(i+1)+1 = ((2*i+1)+1)+1 := by omega
      simpa [paired, he] using ih i (by simpa using hi)

private theorem paired_color (w : List Bool) (i : ℕ) (r : Bool) (hi : i < w.length) :
    colorR (paired w) (pairIndex i r) = colorR w i * layerSign r := by
  cases r with
  | false => simp only [pairIndex, Bool.false_eq_true, ↓reduceIte, add_zero, colorR, paired_get_even w i hi, layerSign, mul_one]
  | true =>
    simp only [pairIndex, ↓reduceIte, colorR, paired_get_odd w i hi]
    cases h : w.getD i false <;> norm_num [color, layerSign]

/-- Explicit ordinary reindexing from the two layer coordinates to interleaved labels. -/
def pairLabelEquiv (m : ℕ) : (Fin m × Bool) ≃ Fin (2*m) where
  toFun p := ⟨pairIndex p.1 p.2, by cases p.2 <;> simp [pairIndex]; omega⟩
  invFun j := (⟨j.val/2, by omega⟩, decide (j.val%2=1))
  left_inv p := by
    rcases p with ⟨i,r⟩
    apply Prod.ext
    · apply Fin.ext
      cases r <;> simp [pairIndex]; omega
    · cases r <;> simp [pairIndex]
  right_inv j := by
    apply Fin.ext
    simp only [pairIndex]
    split_ifs <;> simp_all <;> omega

/-- The paired color word equals the independent block doubling under
ordinary interleaved vertex labels. No switching equivalence is used. -/
theorem paired_is_doubling (w : List Bool) (i j : ℕ) (r s : Bool)
    (hi : i < w.length) (hj : j < w.length) :
    colorGraph (paired w) (pairIndex i r) (pairIndex j s) =
      doublingMatrix (colorGraph w) i r j s := by
  unfold colorGraph
  rw [paired_color w i r hi, paired_color w j s hj]
  have hc : (colorR w i)^2=1 := by unfold colorR color; split <;> norm_num
  dsimp only [doublingMatrix]
  by_cases he : i=j
  · subst j
    cases r <;> cases s <;> simp [pairIndex, layerSign, layerJ, orderSign] <;> nlinarith [hc]
  · cases r <;> cases s <;>
      simp only [pairIndex, layerSign, layerJ, Bool.false_eq_true, ↓reduceIte, ite_eq_right he] <;>
      unfold orderSign <;> split_ifs <;> ring_nf <;> omega

/-- The standard odd cyclic carousel: each vertex beats the next k
vertices in cyclic order. The piecewise form avoids natural subtraction
at the wraparound; equivalence with modular forward distance is proved below. -/
def carouselMatrix (k i j : ℕ) : ℝ :=
  if i = j then 0 else if i < j then (if j ≤ i + k then 1 else -1)
  else (if i ≤ j + k then -1 else 1)

def carouselIndex (k i : ℕ) : ℕ := if i≤k then 2*i else 2*i-(2*k+1)

def carouselInv (k j : ℕ) : ℕ := if j%2=0 then j/2 else (j+(2*k+1))/2

private theorem carouselIndex_lt (k i : ℕ) (hi : i<2*k+1) :
    carouselIndex k i < 2*k+1 := by unfold carouselIndex; split_ifs <;> omega

/-- Multiplication by 2 modulo 2k+1, explicitly realized as an ordinary permutation. -/
def carouselLabelEquiv (k : ℕ) : Fin (2*k+1) ≃ Fin (2*k+1) where
  toFun i := ⟨carouselIndex k i, carouselIndex_lt k i i.isLt⟩
  invFun j := ⟨carouselInv k j, by unfold carouselInv; split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    simp only [carouselIndex, carouselInv]
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    simp only [carouselIndex, carouselInv]
    split_ifs <;> omega

private theorem alternating_color (k i : ℕ) (hi : i<2*k+1) :
    colorR (alternatingOdd k) i = if i%2=0 then 1 else -1 := by
  induction k generalizing i with
  | zero =>
    have he : i=0 := by omega
    subst i
    simp [colorR, alternatingOdd, paired, color]
  | succ k ih =>
    have he : alternatingOdd (k+1) = true::false::alternatingOdd k := by
      simp [alternatingOdd, paired, List.replicate_succ]
    rw [he]
    cases i with
    | zero => simp [colorR, color]
    | succ i =>
      cases i with
      | zero => simp [colorR, color]
      | succ i =>
        have ht := ih i (by omega)
        have hm : (i+1+1)%2=i%2 := by omega
        simpa [colorR, hm] using ht

private theorem carouselIndex_mod (k i : ℕ) (_hi : i<2*k+1) :
    carouselIndex k i % 2 = if i≤k then 0 else 1 := by
  unfold carouselIndex
  split_ifs <;> omega

/-- The explicit ordinary permutation matches the alternating color target
with the standard cyclic forward-k-neighbor carousel. -/
theorem alternating_is_carousel (k i j : ℕ)
    (hi : i<2*k+1) (hj : j<2*k+1) :
    colorGraph (alternatingOdd k) (carouselIndex k i) (carouselIndex k j) =
      carouselMatrix k i j := by
  unfold colorGraph
  rw [alternating_color k _ (carouselIndex_lt k i hi),
      alternating_color k _ (carouselIndex_lt k j hj),
      carouselIndex_mod k i hi, carouselIndex_mod k j hj]
  unfold carouselIndex carouselMatrix orderSign
  split_ifs <;> simp_all <;> norm_num <;> omega

/-- Explicit cyclic-distance characterization, independent of the color model. -/
theorem carousel_forward_distance (k i j : ℕ)
    (hi : i<2*k+1) (hj : j<2*k+1) (hne : i≠j) :
    carouselMatrix k i j = 1 ↔ (j+(2*k+1)-i)%(2*k+1) ≤ k := by
  by_cases hij : i<j
  · have he : j+(2*k+1)-i = (2*k+1)+(j-i) := by omega
    have hd : j-i < 2*k+1 := by omega
    simp only [carouselMatrix, ite_eq_right hne, ite_eq_left hij]
    rw [he]
    simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hd]
    split_ifs <;> norm_num <;> omega
  · have hd : j+(2*k+1)-i < 2*k+1 := by omega
    rw [Nat.mod_eq_of_lt hd]
    simp only [carouselMatrix, ite_eq_right hne, ite_eq_right hij]
    split_ifs <;> norm_num <;> omega

/-- Full finite-label doubling isomorphism. -/
theorem paired_doubling_isomorphism (w : List Bool)
    (p q : Fin w.length × Bool) :
    colorGraph (paired w) (pairLabelEquiv w.length p) (pairLabelEquiv w.length q) =
      doublingMatrix (colorGraph w) p.1 p.2 q.1 q.2 := by
  exact paired_is_doubling w p.1 q.1 p.2 q.2 p.1.isLt q.1.isLt

/-- Full finite-label standard carousel isomorphism. -/
theorem alternating_carousel_isomorphism (k : ℕ) (i j : Fin (2*k+1)) :
    colorGraph (alternatingOdd k) (carouselLabelEquiv k i) (carouselLabelEquiv k j) =
      carouselMatrix k i j := by
  exact alternating_is_carousel k i j i.isLt j.isLt

/-- The ordinary permutation's displayed cyclic formula is exact. -/
theorem carouselIndex_eq_mod (k i : ℕ) (hi : i<2*k+1) :
    carouselIndex k i = (2*i)%(2*k+1) := by
  unfold carouselIndex
  split_ifs with h
  · exact (Nat.mod_eq_of_lt (by omega : 2*i<2*k+1)).symm
  · have he : 2*i = (2*i-(2*k+1))+(2*k+1) := by omega
    have hd : 2*i-(2*k+1)<2*k+1 := by omega
    symm
    calc
      (2*i)%(2*k+1) = ((2*i-(2*k+1))+(2*k+1))%(2*k+1) := congrArg (fun x => x%(2*k+1)) he
      _ = 2*i-(2*k+1) := by simp [Nat.mod_eq_of_lt hd]

#print axioms paired_doubling_isomorphism
#print axioms alternating_carousel_isomorphism
#print axioms carouselIndex_eq_mod
#print axioms paired_is_doubling
#print axioms pairLabelEquiv
#print axioms alternating_is_carousel
#print axioms carouselLabelEquiv
#print axioms carousel_forward_distance
end ColorTransport
