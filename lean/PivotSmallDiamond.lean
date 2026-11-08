import PivotCycleLink
import DiamondTriangleIncidence
noncomputable section
namespace PivotSmallDiamond
open Finset DiamondGap DiamondFreeRepresentation DiamondTriangleIncidence PivotCycleLink
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma sourceSwitch_diamonds (T : Tournament V) (p : V) :
    (sourceSwitch T p).diamonds = T.diamonds := by
  classical
  ext s
  rw [Tournament.mem_diamonds, Tournament.mem_diamonds]
  exact switched_diamond_iff T (pivotSign T p) (pivotSign_sq T p) s

lemma triangles_positive (T : Tournament V) (hD : 0 < T.diamonds.card) :
    0 < (cyclicTriangles T).card := by
  have h := diamonds_le_triangles T
  by_contra hz
  have hz' : (cyclicTriangles T).card = 0 := by omega
  rw [hz',mul_zero] at h
  omega

/-- An actual source switch with positive but small cycle count. D and r here
are genuine unordered-set cardinalities, not free scalar placeholders. -/
theorem exists_small_source_cycles (T : Tournament V)
    (hn : 4 ≤ Fintype.card V) (hD : 0 < T.diamonds.card)
    (hsmall : 24*T.diamonds.card ≤ (Fintype.card V)^2) :
    ∃ p : V,
      0 < (cyclicTriangles (sourceSwitch T p)).card ∧
      Fintype.card V*(cyclicTriangles (sourceSwitch T p)).card ≤ 4*T.diamonds.card ∧
      6*(cyclicTriangles (sourceSwitch T p)).card ≤ Fintype.card V := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p,hp⟩ := exists_pivot_total_cycles T
  refine ⟨p,?_,hp,?_⟩
  · apply triangles_positive
    simpa only [sourceSwitch_diamonds] using hD
  · have hmult : Fintype.card V*(6*(cyclicTriangles (sourceSwitch T p)).card) ≤
        Fintype.card V*Fintype.card V := by nlinarith
    by_contra hnot
    have hl : Fintype.card V+1 ≤ 6*(cyclicTriangles (sourceSwitch T p)).card := by omega
    have hm := Nat.mul_le_mul_left (Fintype.card V) hl
    nlinarith
end PivotSmallDiamond
#print axioms PivotSmallDiamond.exists_small_source_cycles
