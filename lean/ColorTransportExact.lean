import ColorTransport
import ColorEnergy
namespace ColorTransport

private theorem area_heads (a b : Bool) (u v : List Bool) :
    area (a::u) v = area (b::u) v := by cases v <;> rfl

private theorem up_step (t v : List Bool) (b : Bool)
    (hl : t.length = v.length) (hc : v.count true < t.count true) :
    ∃ w, Swaps 1 (false::t) w ∧
      area (false::t) (b::v) = area w (b::v) + 1 := by
  induction t generalizing v b with
  | nil => simp at hc
  | cons a t ih =>
    cases v with
    | nil => simp at hl
    | cons c v =>
      cases a with
      | true =>
        refine ⟨true::false::t, Swaps.swap false true t (by decide), ?_⟩
        have hh := area_heads true false t (c::v)
        simp only [area] at hh ⊢
        simp at hc
        simp only [List.count_cons] at *
        cases c <;> simp at * <;>
          rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)] <;> omega
      | false =>
        have hl' : t.length = v.length := by simpa using hl
        have hc' : v.count true < t.count true := by cases c <;> simp_all; omega
        obtain ⟨w, hw, he⟩ := ih v c hl' hc'
        refine ⟨false::w, Swaps.cons false hw, ?_⟩
        have hp := List.perm_iff_count.mp hw.perm true
        simp only [area]
        rw [← hp]
        simp only [area] at he
        omega

private theorem down_step (t v : List Bool) (b : Bool)
    (hl : t.length = v.length) (hc : t.count true < v.count true) :
    ∃ w, Swaps 1 (true::t) w ∧
      area (true::t) (b::v) = area w (b::v) + 1 := by
  induction t generalizing v b with
  | nil => cases v <;> simp_all
  | cons a t ih =>
    cases v with
    | nil => simp at hl
    | cons c v =>
      cases a with
      | false =>
        refine ⟨false::true::t, Swaps.swap true false t (by decide), ?_⟩
        simp only [area]
        cases c <;> simp at hc ⊢ <;>
          rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)] <;> omega
      | true =>
        have hl' : t.length = v.length := by simpa using hl
        have hc' : t.count true < v.count true := by cases c <;> simp_all; omega
        obtain ⟨w, hw, he⟩ := ih v c hl' hc'
        refine ⟨true::w, Swaps.cons true hw, ?_⟩
        have hp := List.perm_iff_count.mp hw.perm true
        simp only [area]
        rw [← hp]
        simp only [area] at he
        omega

/-- A constructive unit descent step, unless the two actual words coincide. -/
theorem area_descent (u v : List Bool) (hp : u.Perm v) (hne : u ≠ v) :
    ∃ w, Swaps 1 u w ∧ area u v = area w v + 1 := by
  induction u generalizing v with
  | nil => have := hp.length_eq; cases v <;> simp_all
  | cons a u ih =>
    cases v with
    | nil => have := hp.length_eq; simp at this
    | cons b v =>
      by_cases hab : a = b
      · subst b
        have htail : u.Perm v := List.Perm.cons_inv hp
        have hne' : u ≠ v := by intro he; subst v; exact hne rfl
        obtain ⟨w, hw, he⟩ := ih v htail hne'
        refine ⟨a::w, Swaps.cons a hw, ?_⟩
        have hc := List.perm_iff_count.mp hw.perm true
        simp only [area]
        rw [← hc]
        omega
      · have hl : u.length = v.length := by simpa using hp.length_eq
        have hc := List.perm_iff_count.mp hp true
        cases a <;> cases b <;> simp_all
        · exact up_step u v true hl (by omega)
        · exact down_step u v false hl (by omega)

theorem area_nonneg (u v : List Bool) : 0 ≤ area u v := by
  induction u generalizing v with
  | nil => simp [area]
  | cons a u ih =>
    cases v with
    | nil => simp [area]
    | cons b v => exact add_nonneg (abs_nonneg _) (ih v)

/-- The area lower bound is attained by an actual finite swap derivation. -/
theorem exact_swaps (u v : List Bool) (hp : u.Perm v) :
    ∃ n, Swaps n u v ∧ (n : ℤ) = area u v := by
  generalize hN : (area u v).toNat = N
  induction N using Nat.strong_induction_on generalizing u v with
  | h N ih =>
    by_cases heq : u = v
    · subst v
      exact ⟨0, Swaps.refl _, by simp⟩
    · obtain ⟨w, hw, hdrop⟩ := area_descent u v hp heq
      have hwv : w.Perm v := hw.perm.symm.trans hp
      have ha := area_nonneg u v
      have hb := area_nonneg w v
      have hlt : (area w v).toNat < N := by omega
      obtain ⟨n, hn, hnarea⟩ := ih (area w v).toNat hlt w v hwv rfl
      refine ⟨1+n, Swaps.trans hw hn, ?_⟩
      push_cast
      omega

/-- Exact optimality: area is both an attained step count and a lower bound
for every possible adjacent unlike-swap derivation. -/
theorem exact_minimum (u v : List Bool)
    (hlen : u.length = v.length) (hc : charge u = charge v) :
    ∃ n, Swaps n u v ∧ (n : ℤ) = area u v ∧
      ∀ m, Swaps m u v → n ≤ m := by
  obtain ⟨n, hn, he⟩ := exact_swaps u v (perm_of_length_charge hlen hc)
  refine ⟨n, hn, he, ?_⟩
  intro m hm
  have h := area_le_swaps hm
  omega

private theorem count_split (w : List Bool) (i : ℕ) :
    (w.take i).count true + (w.drop i).count true = w.count true := by
  rw [← List.count_append, List.take_append_drop]

private theorem charge_difference (u v : List Bool) (hl : u.length = v.length) :
    charge u - charge v = 2 * ((u.count true : ℤ) - (v.count true : ℤ)) := by
  have hu := counts_sum_length u
  have hv := counts_sum_length v
  unfold charge
  omega

private theorem area_drop_sum (u v : List Bool) (hl : u.length = v.length) :
    area u v = ∑ i ∈ Finset.range u.length,
      |((u.drop (i+1)).count true : ℤ) - ((v.drop (i+1)).count true : ℤ)| := by
  induction u generalizing v with
  | nil => simp [area]
  | cons a u ih =>
    cases v with
    | nil => simp at hl
    | cons b v =>
      have ht := ih v (by simpa using hl)
      simp only [List.length_cons, Finset.sum_range_succ', List.drop_succ_cons,
        List.drop_zero, area]
      rw [ht]
      ring

private theorem prefix_drop_difference (u v : List Bool) (hp : u.Perm v) (i : ℕ) :
    |charge (u.take i) - charge (v.take i)| =
      2 * |((u.drop i).count true : ℤ) - ((v.drop i).count true : ℤ)| := by
  have hl : (u.take i).length = (v.take i).length := by simp [hp.length_eq]
  rw [charge_difference _ _ hl, abs_mul]
  norm_num
  have hu := count_split u i
  have hv := count_split v i
  have hc := List.perm_iff_count.mp hp true
  have he : ((u.take i).count true : ℤ) - ((v.take i).count true : ℤ) =
      -(((u.drop i).count true : ℤ) - ((v.drop i).count true : ℤ)) := by omega
  rw [he, abs_neg]

/-- Exact conversion from the concrete suffix count area to the usual color
prefix area, including the zero final discrepancy. -/
theorem prefix_area_identity (u v : List Bool) (hp : u.Perm v) :
    (∑ i ∈ Finset.range (u.length+1), |charge (u.take i) - charge (v.take i)|) =
      2 * area u v := by
  rw [Finset.sum_range_succ']
  simp only [List.take_zero, sub_self, abs_zero, add_zero]
  simp_rw [prefix_drop_difference u v hp]
  rw [← Finset.mul_sum, area_drop_sum u v hp.length_eq]

/-- A true optimal path whose step count is half the usual prefix-color area. -/
theorem prefix_exact_minimum (u v : List Bool)
    (hl : u.length = v.length) (hc : charge u = charge v) :
    ∃ n, Swaps n u v ∧
      2 * (n : ℤ) = ∑ i ∈ Finset.range (u.length+1),
        |charge (u.take i) - charge (v.take i)| ∧
      ∀ m, Swaps m u v → n ≤ m := by
  obtain ⟨n, hn, he, hmin⟩ := exact_minimum u v hl hc
  refine ⟨n, hn, ?_, hmin⟩
  rw [prefix_area_identity u v (perm_of_length_charge hl hc), he]

private theorem odd_target_prefix (k i : ℕ) (hi : i ≤ 2*k+1) :
    charge ((alternatingOdd k).take i) = (i % 2 : ℕ) := by
  induction k generalizing i with
  | zero =>
    interval_cases i <;> simp [alternatingOdd, paired, charge]
  | succ k ih =>
    have he : alternatingOdd (k+1) = true::false::alternatingOdd k := by
      simp [alternatingOdd, paired, List.replicate_succ]
    rw [he]
    cases i with
    | zero => simp [charge]
    | succ i =>
      cases i with
      | zero => simp [charge]
      | succ i =>
        simp only [List.take_succ_cons, charge_cons]
        have ht := ih i (by omega)
        simp only [color, Bool.false_eq_true, ↓reduceIte] at *
        rw [ht]
        have hm : (i+1+1)%2 = i%2 := by omega
        rw [hm]
        ring

private theorem prefix_parity (w : List Bool) (i : ℕ) (hi : i ≤ w.length) :
    ∃ z : ℤ, charge (w.take i) = 2*z + (i%2 : ℕ) := by
  have hl : (w.take i).length = i := by simp [List.length_take, Nat.min_eq_left hi]
  have hh := counts_sum_length (w.take i)
  refine ⟨charge (w.take i) / 2, ?_⟩
  unfold charge at *
  omega

/-- A real swap path satisfies the odd normalized quadratic repair bound.
This statement uses the actual integer prefix colors of the input word,
not an assumed transport metric or assumed optimal target. -/
theorem odd_repair_path (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k+1) (hc : charge w = 1) :
    ∃ n, Swaps n w (alternatingOdd k) ∧
      2*(n : ℤ) ≤ ∑ i ∈ Finset.range (w.length+1),
        charge (w.take i) * (charge (w.take i)-1) := by
  have hp : w.Perm (alternatingOdd k) := perm_of_length_charge
    (by simpa using hl) (by simpa using hc)
  obtain ⟨n, hn, he⟩ := exact_swaps w (alternatingOdd k) hp
  refine ⟨n, hn, ?_⟩
  have ht := ColorEnergy.odd_prefix_transport_budget (Finset.range (w.length+1))
    (fun i => charge (w.take i)) (fun i => charge ((alternatingOdd k).take i)) ?_
  · rw [prefix_area_identity w (alternatingOdd k) hp, ← he] at ht
    exact ht
  · intro i hi
    have hi' : i ≤ w.length := by simpa using (Finset.mem_range.mp hi)
    obtain ⟨z, hz⟩ := prefix_parity w i hi'
    have htarget := odd_target_prefix k i (by omega)
    have hm : i%2=0 ∨ i%2=1 := by omega
    rcases hm with hm | hm
    · left
      exact ⟨z, by simpa [hm] using hz, by simpa [hm] using htarget⟩
    · right
      exact ⟨z, by simpa [hm] using hz, by simpa [hm] using htarget⟩

/-- Energy-minimizing pair orientations selected from the actual odd prefixes. -/
def repairOrient (w : List Bool) (k : ℕ) : List Bool :=
  List.ofFn (fun j : Fin k => decide (0 < charge (w.take (2*j.val+1))))

private theorem sign_distance (z : ℤ) (hz : z ≠ 0) :
    |z - color (decide (0 < z))| = |z|-1 := by
  by_cases hp : 0 < z
  · simp [color, hp, abs_of_nonneg (by omega : 0 ≤ z-1), abs_of_nonneg (by omega : 0 ≤ z)]
  · have hn : z ≤ -1 := by omega
    simp [color, hp, abs_of_nonpos (by omega : z+1 ≤ 0), abs_of_nonpos (by omega : z ≤ 0)]
    ring

private theorem even_target_local (w : List Bool) (k i : ℕ)
    (hl : w.length = 2*k) (hi : i ≤ w.length) :
    2 * |charge (w.take i) - charge ((paired (repairOrient w k)).take i)| ≤
      (charge (w.take i))^2 - (i%2 : ℕ) := by
  obtain ⟨z, hz⟩ := prefix_parity w i hi
  have hm : i%2=0 ∨ i%2=1 := by omega
  rcases hm with hm | hm
  · have he : i = 2*(i/2) := by omega
    have ht := paired_even_prefix (repairOrient w k) (i/2)
    rw [← he] at ht
    rw [ht, sub_zero, hm]
    simp only [Nat.cast_zero, sub_zero]
    have hp : charge (w.take i) = 2*z := by simpa [hm] using hz
    rw [hp]
    exact ColorEnergy.even_prefix_budget z
  · have he : i = 2*(i/2)+1 := by omega
    have hj : i/2 < k := by omega
    have ht := paired_odd_prefix (repairOrient w k) (i/2) (by simpa [repairOrient] using hj)
    rw [← he] at ht
    have ho : (repairOrient w k).getD (i/2) false =
        decide (0 < charge (w.take i)) := by
      simp [repairOrient, List.getD_eq_getElem?_getD, hj, ← he]
    rw [ho] at ht
    have hp : charge (w.take i) ≠ 0 := by simp only [hm, Nat.cast_one] at hz; omega
    rw [ht, sign_distance _ hp, hm]
    exact ColorEnergy.odd_prefix_budget _ hp

/-- A concrete path to the sign-selected paired target with the even
quadratic repair budget. No swap attainability assumption remains. -/
theorem even_repair_path (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k) (hc : charge w = 0) :
    ∃ n, Swaps n w (paired (repairOrient w k)) ∧
      4*(n : ℤ) ≤ ∑ i ∈ Finset.range (w.length+1),
        ((charge (w.take i))^2 - (i%2 : ℕ)) := by
  have hp : w.Perm (paired (repairOrient w k)) := perm_of_length_charge
    (by simpa [repairOrient] using hl) (by simpa using hc)
  obtain ⟨n, hn, he⟩ := exact_swaps w (paired (repairOrient w k)) hp
  refine ⟨n, hn, ?_⟩
  have ht := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range (w.length+1)) =>
    even_target_local w k i hl (by simpa using (Finset.mem_range.mp hi)))
  rw [← Finset.mul_sum, prefix_area_identity w _ hp, ← he] at ht
  omega

def prefixR (w : List Bool) (i : ℕ) : ℝ := charge (w.take i)
def colorR (w : List Bool) (i : ℕ) : ℝ := color (w.getD i false)

/-- The actual finite row-score expression, using the colors and prefix path
of the word itself, not a freely supplied energy parameter. -/
def wordEnergy (w : List Bool) : ℝ :=
  ColorEnergy.energy w.length (charge w) (prefixR w) (colorR w)

private theorem prefixR_step (w : List Bool) (i : ℕ) (hi : i < w.length) :
    prefixR w (i+1) = prefixR w i + colorR w i := by
  have h : charge (w.take (i+1)) = charge (w.take i) + color (w.getD i false) := by
    rw [List.take_succ_eq_append_getElem hi]
    simp only [charge_eq_sum, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    congr 1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  unfold prefixR colorR
  exact_mod_cast h

private theorem colorR_sq (w : List Bool) (i : ℕ) : (colorR w i)^2 = 1 := by
  unfold colorR color
  split <;> norm_num

/-- Odd repair in the original energy units: an actual path of at most E/8 swaps. -/
theorem odd_energy_repair (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k+1) (hc : charge w = 1) :
    ∃ n, Swaps n w (alternatingOdd k) ∧ (n : ℝ) ≤ wordEnergy w / 8 := by
  obtain ⟨n, hn, hbudget⟩ := odd_repair_path w k hl hc
  refine ⟨n, hn, ?_⟩
  rw [Finset.sum_range_succ] at hbudget
  simp only [List.take_length, hc, sub_self, mul_zero, add_zero] at hbudget
  have hb : 2*(n : ℝ) ≤ ∑ i ∈ Finset.range w.length,
      prefixR w i * (prefixR w i-1) := by
    unfold prefixR
    exact_mod_cast hbudget
  have he := ColorEnergy.odd_energy w.length (prefixR w) (colorR w)
    (by simp [prefixR, charge]) (by simp [prefixR, hc])
    (prefixR_step w) (fun i _ => colorR_sq w i)
  have hwe : wordEnergy w = ColorEnergy.energy w.length 1 (prefixR w) (colorR w) := by
    simp [wordEnergy, hc]
  rw [hwe, he]
  linarith

private theorem parity_sum (k : ℕ) :
    (∑ i ∈ Finset.range (2*k+1), ((i%2 : ℕ) : ℤ)) = k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have he : 2*(k+1)+1 = (2*k+1)+1+1 := by omega
    rw [he, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h₁ : (2*k+1)%2=1 := by omega
    have h₂ : (2*k+1+1)%2=0 := by omega
    simp only [h₁, h₂, Nat.cast_zero, Nat.cast_one, add_zero, Nat.cast_add]

/-- Even repair in the original excess units e = E - length:
a real path to an explicitly constructed paired word of at most e/16 swaps. -/
theorem even_energy_repair (w : List Bool) (k : ℕ)
    (hl : w.length = 2*k) (hc : charge w = 0) :
    ∃ n, Swaps n w (paired (repairOrient w k)) ∧
      (n : ℝ) ≤ (wordEnergy w - w.length) / 16 := by
  obtain ⟨n, hn, hbudget⟩ := even_repair_path w k hl hc
  refine ⟨n, hn, ?_⟩
  rw [Finset.sum_sub_distrib] at hbudget
  have hp : (∑ i ∈ Finset.range (w.length+1), ((i%2 : ℕ) : ℤ)) = k := by
    rw [hl]
    exact parity_sum k
  rw [hp, Finset.sum_range_succ] at hbudget
  simp only [List.take_length, hc, zero_pow (by decide : 2 ≠ 0), add_zero] at hbudget
  have hb : 4*(n : ℝ) ≤ (∑ i ∈ Finset.range w.length, (prefixR w i)^2) - k := by
    unfold prefixR
    exact_mod_cast hbudget
  have he := ColorEnergy.even_energy w.length (prefixR w) (colorR w)
    (by simp [prefixR, charge]) (by simp [prefixR, hc])
    (prefixR_step w) (fun i _ => colorR_sq w i)
  have hwe : wordEnergy w = ColorEnergy.energy w.length 0 (prefixR w) (colorR w) := by
    simp [wordEnergy, hc]
  rw [hwe, he]
  have hlen : (w.length : ℝ) = 2*(k : ℝ) := by exact_mod_cast hl
  linarith

#print axioms odd_energy_repair
#print axioms even_energy_repair
#print axioms even_repair_path
#print axioms odd_repair_path
#print axioms prefix_area_identity
#print axioms prefix_exact_minimum
#print axioms exact_swaps
#print axioms exact_minimum
#print axioms area_descent
end ColorTransport
