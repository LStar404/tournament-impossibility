import OrdinalSixthPolynomial
noncomputable section
namespace OrdinalMomentRecurrence
open Finset OrdinalSixthPolynomial

structure Packet where
  size : ℝ
  first : ℝ
  second : ℝ
  sixth : ℝ

def join (a b : Packet) : Packet where
  size := a.size+b.size
  first := a.first+b.first+a.size*b.size*(a.size+b.size)
  second := a.second+b.second+(b.size^2+2*a.size*b.size)*a.first+
    (a.size^2+2*a.size*b.size)*b.first+a.size^2*b.size^2*(a.size+b.size)
  sixth := a.sixth+b.sixth+6*b.size*a.second+6*a.size*b.second+
    6*a.first*b.first+6*a.size*b.size^2*a.first+
    6*a.size^2*b.size*b.first+2*a.size^3*b.size^3

def alpha (a : Packet) := a.size^3/3-a.first
def beta (a : Packet) := a.second-a.size^2*a.first+a.size^5/5
def gamma (a : Packet) := a.sixth/6-a.size*a.second-a.first^2/2+
  a.size^3*a.first-a.size^6/6

lemma alpha_join (a b : Packet) : alpha (join a b) = alpha a+alpha b := by
  unfold alpha join; dsimp; ring
lemma beta_join (a b : Packet) : beta (join a b) = beta a+beta b := by
  unfold beta join; dsimp; ring
lemma gamma_join (a b : Packet) : gamma (join a b) = gamma a+gamma b := by
  unfold gamma join; dsimp; ring

lemma reconstruct (a : Packet) :
    a.sixth/6 = gamma a+a.size*beta a+(alpha a)^2/2-
      a.size^3*alpha a/3+a.size^6/45 := by
  unfold alpha beta gamma
  ring

def cumulative (p : ℕ → Packet) : ℕ → Packet
  | 0 => ⟨0,0,0,0⟩
  | k+1 => join (cumulative p k) (p k)

lemma cumulative_size (p : ℕ → Packet) (k : ℕ) :
    (cumulative p k).size = ∑ i ∈ range k, (p i).size := by
  induction k with
  | zero => simp [cumulative]
  | succ k ih => simp [cumulative, join, sum_range_succ, ih]
lemma cumulative_alpha (p : ℕ → Packet) (k : ℕ) :
    alpha (cumulative p k) = ∑ i ∈ range k, alpha (p i) := by
  induction k with
  | zero => simp [cumulative, alpha]
  | succ k ih => rw [cumulative, alpha_join, sum_range_succ, ih]
lemma cumulative_beta (p : ℕ → Packet) (k : ℕ) :
    beta (cumulative p k) = ∑ i ∈ range k, beta (p i) := by
  induction k with
  | zero => simp [cumulative, beta]
  | succ k ih => rw [cumulative, beta_join, sum_range_succ, ih]
lemma cumulative_gamma (p : ℕ → Packet) (k : ℕ) :
    gamma (cumulative p k) = ∑ i ∈ range k, gamma (p i) := by
  induction k with
  | zero => simp [cumulative, gamma]
  | succ k ih => rw [cumulative, gamma_join, sum_range_succ, ih]

/-- Algebraic reconstruction from the explicitly defined two-block recurrence.
A matrix realization of `join` is a separate theorem, not an implicit assumption. -/
theorem cumulative_sixth (p : ℕ → Packet) (k : ℕ) :
    (cumulative p k).sixth = 6*coefficient (range k)
      (∑ i ∈ range k, (p i).size) (fun i => (p i).size)
      (fun i => (p i).first) (fun i => (p i).second) (fun i => (p i).sixth) := by
  have h := reconstruct (cumulative p k)
  rw [cumulative_size, cumulative_alpha, cumulative_beta, cumulative_gamma] at h
  unfold coefficient cubic quintic alpha beta gamma at *
  linarith
end OrdinalMomentRecurrence
