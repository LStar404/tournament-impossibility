import DiamondLinkAverage
import DiamondTriangleIncidence
noncomputable section
namespace PivotCycleLink
open Finset DiamondGap DiamondFreeRepresentation DiamondLinkAverage
variable {V : Type*} [Fintype V] [DecidableEq V]

def sourceSwitch (T : Tournament V) (p : V) : Tournament V :=
  switched T (pivotSign T p) (pivotSign_sq T p)

def cyclesAway (U : Tournament V) (p : V) : Finset (Finset V) :=
  by classical exact (univ.powerset).filter (fun s => p ∉ s ∧ DiamondTriangleIncidence.IsCyclic U s)

lemma mem_cyclesAway (U : Tournament V) (p : V) (s : Finset V) :
    s ∈ cyclesAway U p ↔ p ∉ s ∧ DiamondTriangleIncidence.IsCyclic U s := by
  classical
  simp [cyclesAway]

lemma switched_diamond_iff (T : Tournament V) (d : V → ℤ) (hd : ∀ x, d x^2=1)
    (s : Finset V) : (switched T d hd).IsDiamond s ↔ T.IsDiamond s := by
  constructor
  · rintro ⟨hc,a,b,c,e,he,hq⟩
    refine ⟨hc,a,b,c,e,he,?_⟩
    simpa only [switched_quad_sq] using hq
  · rintro ⟨hc,a,b,c,e,he,hq⟩
    refine ⟨hc,a,b,c,e,he,?_⟩
    simpa only [switched_quad_sq] using hq

lemma move_second (T : Tournament V) (a b c d : V) :
    T.quad b a c d ^2 = T.quad a b c d ^2 := by
  unfold Tournament.quad pf
  rw [T.skew b a]
  ring
lemma move_third (T : Tournament V) (a b c d : V) :
    T.quad c a b d ^2 = T.quad a b c d ^2 := by
  unfold Tournament.quad pf
  rw [T.skew c a, T.skew c b]
  ring
lemma move_fourth (T : Tournament V) (a b c d : V) :
    T.quad d a b c ^2 = T.quad a b c d ^2 := by
  unfold Tournament.quad pf
  rw [T.skew d a, T.skew d b, T.skew d c]
  ring

lemma diamond_witness_at (U : Tournament V) (p : V) (s : Finset V)
    (hd : U.IsDiamond s) (hp : p ∈ s) :
    ∃ a b c, s={p,a,b,c} ∧ U.quad p a b c ^2=9 := by
  rcases hd with ⟨hc,a,b,c,d,hs,hq⟩
  rw [hs] at hp
  simp only [mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨b,c,d,hs,hq⟩
  · refine ⟨a,c,d,?_,?_⟩
    · simpa [insert_comm] using hs
    · rw [move_second]; exact hq
  · refine ⟨a,b,d,?_,?_⟩
    · rw [hs]; ext x; simp only [mem_insert, mem_singleton]; tauto
    · rw [move_third]; exact hq
  · refine ⟨a,b,c,?_,?_⟩
    · rw [hs]; ext x; simp only [mem_insert, mem_singleton]; tauto
    · rw [move_fourth]; exact hq

lemma source_quad_cycle (U : Tournament V) (p a b c : V)
    (hs : ∀ x, x ≠ p → U.S p x=1) (hq : U.quad p a b c ^2=9) :
    (U.S a b=1 ∧ U.S b c=1 ∧ U.S c a=1) ∨
    (U.S a c=1 ∧ U.S c b=1 ∧ U.S b a=1) := by
  have hd := U.quad_distinct p a b c hq
  have hpa := hs a (Ne.symm hd.1)
  have hpb := hs b (Ne.symm hd.2.1)
  have hpc := hs c (Ne.symm hd.2.2.1)
  rcases U.unit a b hd.2.2.2.1 with hab | hab <;>
    rcases U.unit a c hd.2.2.2.2.1 with hac | hac <;>
    rcases U.unit b c hd.2.2.2.2.2 with hbc | hbc
  all_goals simp only [Tournament.quad, pf, hpa,hpb,hpc,hab,hac,hbc] at hq
  all_goals norm_num at hq
  all_goals simp [hab,hac,hbc,U.skew c a,U.skew c b,U.skew b a]

lemma source_diamond_erase_cycle (U : Tournament V) (p : V)
    (hs : ∀ x, x ≠ p → U.S p x=1) (s : Finset V)
    (hd : U.IsDiamond s) (hp : p ∈ s) : DiamondTriangleIncidence.IsCyclic U (s.erase p) := by
  apply (DiamondTriangleIncidence.isCyclic_iff_positive U (s.erase p)).mpr
  obtain ⟨a,b,c,he,hq⟩ := diamond_witness_at U p s hd hp
  have hdist := U.quad_distinct p a b c hq
  have herase : s.erase p = {a,b,c} := by
    rw [he]
    simp [hdist.1,hdist.2.1,hdist.2.2.1,Ne.symm hdist.1,Ne.symm hdist.2.1,Ne.symm hdist.2.2.1]
  refine ⟨?_,?_⟩
  · rw [card_erase_of_mem hp, hd.1]
  · rcases source_quad_cycle U p a b c hs hq with hc | hc
    · exact ⟨a,b,c,herase,hc⟩
    · refine ⟨a,c,b,?_,hc⟩
      rw [herase]; ext x; simp only [mem_insert, mem_singleton]; tauto

lemma source_cycle_insert_diamond (U : Tournament V) (p : V)
    (hs : ∀ x, x ≠ p → U.S p x=1) (s : Finset V)
    (hc : DiamondTriangleIncidence.IsCyclic U s) (hp : p ∉ s) : U.IsDiamond (insert p s) := by
  rcases (DiamondTriangleIncidence.isCyclic_iff_positive U s).mp hc with ⟨hcard,a,b,c,he,hab,hbc,hca⟩
  have hpa : a ≠ p := by intro h; apply hp; rw [he]; simp [h]
  have hpb : b ≠ p := by intro h; apply hp; rw [he]; simp [h]
  have hpc : c ≠ p := by intro h; apply hp; rw [he]; simp [h]
  have hac : U.S a c = -1 := by rw [U.skew a c,hca]
  have hq : U.quad p a b c ^2=9 := by
    simp [Tournament.quad,pf,hs a hpa,hs b hpb,hs c hpc,hab,hbc,hac]
  simpa [he] using U.diamond_of_quad p a b c hq

/-- Erasing the source pivot is a genuine bijection of unordered sets. -/
theorem cycles_eq_link_image (T : Tournament V) (p : V) :
    cyclesAway (sourceSwitch T p) p = (link T p).image (fun s => s.erase p) := by
  classical
  ext s
  constructor
  · intro hs
    obtain ⟨hp,hc⟩ := (mem_cyclesAway _ _ _).mp hs
    have hd := source_cycle_insert_diamond (sourceSwitch T p) p
      (pivot_source T p) s hc hp
    have hd' : T.IsDiamond (insert p s) :=
      (switched_diamond_iff T _ _ _).mp hd
    refine mem_image.mpr ⟨insert p s,?_,?_⟩
    · exact (mem_link T p _).mpr ⟨hd',by simp⟩
    · simp [hp]
  · intro hs
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hs
    obtain ⟨hd,hp⟩ := (mem_link T p q).mp hq
    have hd' : (sourceSwitch T p).IsDiamond q :=
      (switched_diamond_iff T _ _ _).mpr hd
    apply (mem_cyclesAway _ _ _).mpr
    exact ⟨by simp, source_diamond_erase_cycle _ p (pivot_source T p) q hd' hp⟩

theorem cycle_count_eq_link (T : Tournament V) (p : V) :
    (cyclesAway (sourceSwitch T p) p).card = (link T p).card := by
  classical
  rw [cycles_eq_link_image]
  apply card_image_of_injOn
  intro s hs t ht he
  have hps := ((mem_link T p s).mp hs).2
  have hpt := ((mem_link T p t).mp ht).2
  have hh := congrArg (insert p) he
  simpa [insert_erase hps,insert_erase hpt] using hh

lemma cyclic_avoids_source (U : Tournament V) (p : V)
    (hs : ∀ x, x ≠ p → U.S p x=1) (s : Finset V)
    (hc : DiamondTriangleIncidence.IsCyclic U s) : p ∉ s := by
  have hno (x : V) : U.S x p ≠ 1 := by
    by_cases hx : x=p
    · subst x; rw [U.diagonal]; norm_num
    · rw [U.skew x p,hs x hx]; norm_num
  obtain ⟨_,a,b,c,he,hab,hbc,hca⟩ := (DiamondTriangleIncidence.isCyclic_iff_positive U s).mp hc
  intro hp
  rw [he] at hp
  simp only [mem_insert,mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact hno c hca
  · exact hno a hab
  · exact hno b hbc

lemma source_cyclesAway_eq_all (T : Tournament V) (p : V) :
    cyclesAway (sourceSwitch T p) p = DiamondTriangleIncidence.cyclicTriangles (sourceSwitch T p) := by
  classical
  ext s
  rw [mem_cyclesAway,DiamondTriangleIncidence.mem_cyclicTriangles]
  exact ⟨fun h => h.2, fun h => ⟨cyclic_avoids_source _ p (pivot_source T p) s h,h⟩⟩

/-- There is a source switch whose remaining actual tournament has r cycles
with n*r≤4D, counting unordered cyclic triangles and unordered diamonds. -/
theorem exists_pivot_few_cycles [Nonempty V] (T : Tournament V) :
    ∃ p : V, Fintype.card V * (cyclesAway (sourceSwitch T p) p).card ≤
      4*T.diamonds.card := by
  obtain ⟨p,hp⟩ := exists_small_link T
  exact ⟨p,by simpa only [cycle_count_eq_link] using hp⟩

/-- Same bound in the common all-triples API: the new source lies in no cycle. -/
theorem exists_pivot_total_cycles [Nonempty V] (T : Tournament V) :
    ∃ p : V, Fintype.card V *
      (DiamondTriangleIncidence.cyclicTriangles (sourceSwitch T p)).card ≤ 4*T.diamonds.card := by
  obtain ⟨p,hp⟩ := exists_pivot_few_cycles T
  exact ⟨p,by simpa only [source_cyclesAway_eq_all] using hp⟩

end PivotCycleLink
#print axioms PivotCycleLink.cycle_count_eq_link
#print axioms PivotCycleLink.exists_pivot_few_cycles

#print axioms PivotCycleLink.exists_pivot_total_cycles
