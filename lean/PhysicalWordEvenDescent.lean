import PhysicalWordRecurrence

noncomputable section
attribute [local instance] Classical.typeDecidableEq
namespace PhysicalWordEvenDescent
open OccurrenceWordDerivative PhysicalTiltedCovariance PhysicalWordRecurrence
variable {I S : Type*} [Fintype I] [Field S] [CharZero S]

/-- A terminating occurrence recurrence in z, independently constructed before
identifying it with the existing u-scaled tilted insertion. -/
def moment (K A : I → I → S) (h : I → S) (w : List I) : PowerSeries S :=
  match w with
  | [] => 1
  | i::v => mean K A h i * moment K A h v +
      ((deletions v).attach.map (fun p => covariance K A i p.val.1 * moment K A h p.val.2)).sum
termination_by w.length
decreasing_by
  · simp
  · have hh := deletion_length _ _ p.property
    simp only [List.length_cons]
    omega

theorem moment_nil (K A : I → I → S) (h : I → S) : moment K A h []=1 := by
  rw [moment]

theorem moment_cons (K A : I → I → S) (h : I → S) (i : I) (w : List I) :
    moment K A h (i::w) = mean K A h i * moment K A h w +
      ((deletions w).map (fun p => covariance K A i p.1 * moment K A h p.2)).sum := by
  rw [moment]
  congr 1
  exact congrArg List.sum (List.attach_map_val (l := deletions w)
    (f := fun p : I × List I => covariance K A i p.1 * moment K A h p.2))

theorem expand_moment (K : I → I → S) (hs : ∀ i j,K i j=K j i)
    (h : I → S) (A : I → I → S) (hA : ∀ i j,A i j=A j i) (w : List I) :
    PowerSeries.expand 2 (by decide) (moment K A h w) = physical K hs h A w := by
  induction w using (measure (fun w : List I => w.length)).wf.induction with
  | h w ih =>
    cases w with
    | nil => simp [moment_nil,physical_nil]
    | cons i w =>
      rw [moment_cons,map_add,map_mul,expand_mean,
        ih w (by change w.length < (i::w).length; simp),recurrence K hs h A hA]
      congr 1
      rw [map_list_sum]
      simp only [List.map_map,Function.comp_def,map_mul,expand_covariance]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      rw [ih p.2 (by change p.2.length < (i::w).length; have hh := deletion_length w p hp; simp only [List.length_cons]; omega)]

end PhysicalWordEvenDescent
#print axioms PhysicalWordEvenDescent.expand_moment
