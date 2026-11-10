import FJPeriodicJumpRadial
import FJRadialFinite

/-! Shared candidate; see focused/runs/final62/result.json for validation. Finite coefficient gluing (M0), followed by the abstract
F/J-to-real-radial theorem. None of these hypotheses is asserted for the
actual normalized extremal tournament sequence. Only finitely many fixed
valuation classes and one uniform jump estimate enter each radial layer. -/
noncomputable section
open Filter Topology Finset
namespace FJFiniteValuationGlue
open FJRadialFinite FJLaurentRadial FJPeriodicJumpRadial

lemma valuationClass_unique {s t n : ℕ}
    (hs : valuationClass s n) (ht : valuationClass t n) : s=t := by
  rcases lt_trichotomy s t with h | h | h
  · exact False.elim (hs.2 ((pow_dvd_pow (2 : ℕ) (by omega : s+1 ≤ t)).trans ht.1))
  · exact h
  · exact False.elim (ht.2 ((pow_dvd_pow (2 : ℕ) (by omega : t+1 ≤ s)).trans hs.1))

lemma valuationClass_not_deep {r s n : ℕ} (hs : s<r)
    (hn : valuationClass s n) : ¬2^r∣n := by
  intro hd
  exact hn.2 ((pow_dvd_pow (2 : ℕ) (by omega : s+1 ≤ r)).trans hd)

lemma exists_shallow_valuation (r n : ℕ) (hn : ¬2^r∣n) :
    ∃ s<r,valuationClass s n := by
  revert hn
  induction r with
  | zero => intro hn; exact False.elim (hn (by simp))
  | succ r ih =>
    intro hn
    by_cases hd : 2^r∣n
    · exact ⟨r,by omega,hd,hn⟩
    · obtain ⟨s,hs,hclass⟩ := ih hd
      exact ⟨s,by omega,hclass⟩

lemma valuationClass_add_period {r s n : ℕ} (hs : s<r) :
    valuationClass s (n+2^r) ↔ valuationClass s n := by
  have h₁ : 2^s∣2^r := pow_dvd_pow (2 : ℕ) (by omega)
  have h₂ : 2^(s+1)∣2^r := pow_dvd_pow (2 : ℕ) (by omega)
  simp only [valuationClass,(Nat.dvd_add_iff_left h₁).symm,
    (Nat.dvd_add_iff_left h₂).symm]

/-- Explicit finite profile. Deep residues share the coefficients from J;
shallow residues use their unique fixed-valuation coefficient vector. -/
def profile (r : ℕ) (α : ℕ→ℕ→ℂ) (β : ℕ→ℂ) (j n : ℕ) : ℂ := by
  classical
  exact if 2^r∣n then β j else
    ∑ s∈range r,if valuationClass s n then α s j else 0

lemma profile_periodic (r : ℕ) (α : ℕ→ℕ→ℂ) (β : ℕ→ℂ) (j : ℕ) :
    Function.Periodic (profile r α β j) (2^r) := by
  intro n
  have hd : 2^r∣n+2^r ↔ 2^r∣n := (Nat.dvd_add_iff_left (dvd_refl (2^r))).symm
  unfold profile
  simp only [hd]
  split_ifs with hn
  · rfl
  · apply Finset.sum_congr rfl
    intro s hs
    have heq := valuationClass_add_period (r := r) (s := s) (n := n) (Finset.mem_range.mp hs)
    by_cases hc : valuationClass s n
    · simp only [if_pos hc, if_pos (heq.mpr hc)]
    · simp only [if_neg hc, if_neg (fun h => hc (heq.mp h))]

lemma profile_at_shallow {r s n : ℕ} (hs : s<r) (hn : valuationClass s n)
    (α : ℕ→ℕ→ℂ) (β : ℕ→ℂ) (j : ℕ) : profile r α β j n=α s j := by
  classical
  rw [profile,if_neg (valuationClass_not_deep hs hn),Finset.sum_eq_single s]
  · simp [hn]
  · intro t ht hts
    have hnot : ¬valuationClass t n := fun ht' => hts (valuationClass_unique ht' hn)
    simp [hnot]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hs))

/-- Fixed F estimates plus the genuinely uniform J estimate yield a single
periodic coefficient jet. No infinite-depth uniformity is required of F. -/
theorem fixedValuation_uniformJump_jet (a : ℕ→ℂ) (r : ℕ) (κ : ℂ)
    (hF : FixedValuationExpansion a) (hJ : UniformJumpAt a r κ) :
    PeriodicJumpJet a (2^r) (2*r) κ := by
  classical
  have hFin : ∀ s : ℕ,∃ α : ℕ→ℂ,∃ C : ℝ,∃ N : ℕ,
      0 ≤ C ∧ ∀ n,N ≤ n → 0<n → valuationClass s n →
        ‖a n-inverseJet α (2*r+1) n‖ ≤ C/(n : ℝ)^(2*r+2) := by
    intro s
    obtain ⟨α,C,hC,N,hN⟩ := hF s (2*r+1)
    exact ⟨α,C,N,hC,by simpa only [show 2*r+1+1=2*r+2 by omega] using hN⟩
  choose α C N hC hN using hFin
  obtain ⟨β,CJ,hCJ,NJ,hNJ⟩ := hJ
  let K : ℝ := CJ+∑ s∈range r,C s
  let M : ℕ := NJ+∑ s∈range r,N s
  have hsum : 0 ≤ ∑ s∈range r,C s := Finset.sum_nonneg (fun s _ => hC s)
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have hCJle : CJ ≤ K := by dsimp [K]; linarith
  have hCle : ∀ s<r,C s ≤ K := by
    intro s hs
    have hcs : C s ≤ ∑ t∈range r,C t :=
      Finset.single_le_sum (fun t _ => hC t) (Finset.mem_range.mpr hs)
    dsimp [K]
    linarith
  have hNJle : NJ ≤ M := by dsimp [M]; omega
  have hNle : ∀ s<r,N s ≤ M := by
    intro s hs
    have hns : N s ≤ ∑ t∈range r,N t :=
      Finset.single_le_sum (fun t _ => Nat.zero_le (N t)) (Finset.mem_range.mpr hs)
    dsimp [M]
    omega
  have hq : 2*2^r=2^(r+1) := by rw [pow_succ]; omega
  refine ⟨profile r α β,fun j _ => profile_periodic r α β j,K,hK,M,?_⟩
  intro n hMn hn
  by_cases hd : 2^r∣n
  · have he : (∑ j∈range (2*r+2),profile r α β j n/(n : ℂ)^j)=
        inverseJet β (2*r+1) n := by
      simp only [profile,if_pos hd,inverseJet]
    rw [he,hq]
    exact (hNJ n (hNJle.trans hMn) hn hd).trans
      (div_le_div_of_nonneg_right hCJle (by positivity))
  · obtain ⟨s,hs,hsn⟩ := exists_shallow_valuation r n hd
    have hp : ¬2*2^r∣n := by
      intro hp
      exact hd ((dvd_mul_left (2^r) 2).trans hp)
    have he : (∑ j∈range (2*r+2),profile r α β j n/(n : ℂ)^j)=
        inverseJet (α s) (2*r+1) n := by
      unfold inverseJet
      apply Finset.sum_congr (by congr 1 <;> omega)
      intro j _
      rw [profile_at_shallow hs hsn]
    rw [he,if_neg hp,sub_zero]
    exact (hN s n ((hNle s hs).trans hMn) hn hsn).trans
      (div_le_div_of_nonneg_right (hCle s hs) (by positivity))

/-- The abstract F/J theorem concludes genuine derivatives and a convergent
regular part. F and J remain explicit coefficient hypotheses. Coefficient boundedness
and all interior derivative identities are derived in the analytic bridge. -/
theorem fixedValuation_uniformJump_radial (a : ℕ→ℂ) (r : ℕ) (κ ω : ℂ)
    (hF : FixedValuationExpansion a)
    (hJ : UniformJumpAt a r κ) (hω : IsPrimitiveRoot ω (2^(r+1))) :
    (∀ h<2*r,FiniteLimit (iteratedDeriv h (radialAt a ω))) ∧
      FiniteLimit (fun x : ℝ => iteratedDeriv (2*r) (radialAt a ω) x-
        (κ/(2^(r+1) : ℕ))*(Real.log (1-x) : ℂ)) := by
  have hq : 2*2^r=2^(r+1) := by rw [pow_succ]; omega
  have hp : IsPrimitiveRoot ω (2*2^r) := by rwa [hq]
  simpa only [hq] using periodicJumpJet_radial a
    (show 0<2^r by positivity) κ ω hp (fixedValuation_uniformJump_jet a r κ hF hJ)

/-- The coefficient jump has exactly the radial amplitude in condition R.
There is no extra root-of-unity factor because the derivative is already
that of the composed real function x ↦ ∑ a_n (ω x)^n. -/
lemma jump_amplitude (r : ℕ) (hr : 1 ≤ r) (L : ℂ) :
    ((2 : ℂ)^(r*(r+1))*L)/(2^(r+1) : ℕ)=L*(2 : ℂ)^(r*r-1) := by
  have hr2 : 1 ≤ r*r := by nlinarith
  have he : r*(r+1)=(r*r-1)+(r+1) := by
    calc
      r*(r+1)=r*r+r := by ring
      _ = (r*r-1)+(r+1) := by omega
  push_cast
  rw [he,pow_add]
  field_simp <;> ring

/-- Exact R amplitude, still conditional on the actual coefficient-side F/J
premises. This does not instantiate them for tournament extremal counts. -/
theorem fixedValuation_uniformJump_R (a : ℕ→ℂ) (r : ℕ) (hr : 1 ≤ r) (L ω : ℂ)
    (hF : FixedValuationExpansion a)
    (hJ : UniformJumpAt a r ((2 : ℂ)^(r*(r+1))*L))
    (hω : IsPrimitiveRoot ω (2^(r+1))) :
    (∀ h<2*r,FiniteLimit (iteratedDeriv h (radialAt a ω))) ∧
      FiniteLimit (fun x : ℝ => iteratedDeriv (2*r) (radialAt a ω) x-
        (L*(2 : ℂ)^(r*r-1))*(Real.log (1-x) : ℂ)) := by
  simpa only [jump_amplitude r hr L] using
    fixedValuation_uniformJump_radial a r ((2 : ℂ)^(r*(r+1))*L) ω hF hJ hω

end FJFiniteValuationGlue
#print axioms FJFiniteValuationGlue.fixedValuation_uniformJump_jet
#print axioms FJFiniteValuationGlue.fixedValuation_uniformJump_radial

#print axioms FJFiniteValuationGlue.jump_amplitude
#print axioms FJFiniteValuationGlue.fixedValuation_uniformJump_R
