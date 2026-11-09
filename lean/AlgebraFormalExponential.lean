import MixedFormalTimeDerivative

noncomputable section
namespace AlgebraFormalExponential
open FormalDividedPowers FormalMixedExponential MixedFormalTimeDerivative
variable {S P : Type*} [Field S] [CharZero S] [CommRing P] [Algebra S P]

include S in
theorem unique (a f g : PowerSeries P)
    (hf : PowerSeries.derivative f=a*f) (hg : PowerSeries.derivative g=a*g)
    (h0 : f.constantCoeff=g.constantCoeff) : f=g := by
  ext m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simpa using h0
    | succ n =>
      have hp : (a*f).coeff n=(a*g).coeff n := by
        simp only [PowerSeries.coeff_mul]
        apply Finset.sum_congr rfl
        intro ij hij
        have hj : ij.2 < n+1 := by
          have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
          omega
        rw [ih ij.2 hj]
      rw [← hf,← hg,PowerSeries.coeff_derivative,PowerSeries.coeff_derivative] at hp
      have hq : (n+1:S) • f.coeff (n+1)=(n+1:S) • g.coeff (n+1) := by
        simpa [Algebra.smul_def,mul_comm] using hp
      have hn : (n+1:S) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hh := congrArg (fun x : P => (n+1:S)⁻¹ • x) hq
      simpa [smul_smul,hn] using hh

theorem exponential_zero : exponential (S:=S) (0:P)=1 := by
  apply unique (S:=S) 0
  · simpa using exponential_time_derivative (S:=S) (0:P)
  · simp
  · simp only [map_mul,← PowerSeries.coeff_zero_eq_constantCoeff_apply,coeff_exponential,divided_zero,PowerSeries.coeff_zero_one,one_mul]

theorem exponential_add (a b : P) :
    exponential (S:=S) (a+b)=exponential (S:=S) a*exponential (S:=S) b := by
  apply unique (S:=S) (PowerSeries.C (a+b))
  · exact exponential_time_derivative _
  · rw [Derivation.leibniz,exponential_time_derivative,exponential_time_derivative]
    simp only [smul_eq_mul,map_add]
    ring
  · simp only [map_mul,← PowerSeries.coeff_zero_eq_constantCoeff_apply,coeff_exponential,divided_zero,PowerSeries.coeff_zero_one,one_mul]

theorem exponential_opposite (a : P) :
    exponential (S:=S) a*exponential (S:=S) (-a)=1 := by
  rw [← exponential_add,add_neg_cancel,exponential_zero]

theorem mixed_zero : mixed (S:=S) (0:P) 0=1 := by
  simp [mixed,exponential_zero]

theorem mixed_add (a b c d : P) :
    mixed (S:=S) (a+c) (b+d)=mixed (S:=S) a b*mixed (S:=S) c d := by
  simp only [mixed,exponential_add,map_mul]
  ring

theorem mixed_opposite (a b : P) :
    mixed (S:=S) a b*mixed (S:=S) (-a) (-b)=1 := by
  rw [← mixed_add,add_neg_cancel,add_neg_cancel,mixed_zero]

theorem mixed_sum {J : Type*} (s : Finset J) (a b : J → P) :
    mixed (S:=S) (∑ i∈s,a i) (∑ i∈s,b i)=∏ i∈s,mixed (S:=S) (a i) (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mixed_zero]
  | @insert i s hi ih => simp [hi,mixed_add,ih]

end AlgebraFormalExponential
#print axioms AlgebraFormalExponential.mixed_sum
#print axioms AlgebraFormalExponential.mixed_opposite
