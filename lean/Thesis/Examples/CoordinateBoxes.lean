import Thesis.Causality.CoordinateBoxes

namespace Thesis.Causality.Examples.CoordinateBoxes

open PetriNet
open Thesis.Causality.CoordinateBoxes

/-!
# Box-splitting and list-replacement regressions

The examples distinguish the actual well-founded relation from tempting
scalar substitutes. Splitting a bounded three-dimensional box increases
the aggregate finite-cap sum from 30 to 87. Splitting an entirely unbounded
box increases the aggregate number of free coordinates from 3 to 6. Each
individual child still has a strictly smaller lexicographic rank.

An overlapping, unchanged box deliberately retains the selected point.
The exact complement theorem is local; the global invariant only promises
coverage of points outside the basis's upward closure. Empty dimensions,
zero bounds, repeated children and literal middle-list updates are checked
without any backward solver, native-decision axiom or probability assumption.
-/

def cube : Box 3 := fun _ => some 10
def selected : Marking 3 := fun _ => 9
def freeCube : Box 3 := fun _ => none

theorem selected_inside : Contains cube selected := fun _ => by
  change 9 < 10
  decide +kernel

theorem selected_inside_free : Contains freeCube selected := fun _ => True.intro

theorem bounded_rank : rank cube = (0, 30) := by decide +kernel

theorem bounded_children_aggregate :
    ((split cube selected).map (fun child => (rank child).2)).sum = 87 := by decide +kernel

theorem free_rank : rank freeCube = (3, 0) := by decide +kernel

theorem free_children_aggregate :
    ((split freeCube selected).map (fun child => (rank child).1)).sum = 6 := by decide +kernel

/-- Bounding a free coordinate may increase the finite budget by an
arbitrarily large amount; the first rank component is decisive. -/
theorem free_cut_rank : rank (cut freeCube 0 1000000) = (2, 1000000) := by decide +kernel

theorem free_cut_decreases : RankBelow (cut freeCube 0 1000000) freeCube :=
  cut_rank_lt freeCube (fun _ => 1000000) (fun _ => True.intro) 0

theorem every_bounded_child_decreases {child : Box 3} (listed : child ∈ split cube selected) :
    RankBelow child cube := split_rank_lt cube selected selected_inside listed

theorem split_with_literal_context :
    WorkStep 3 ([freeCube] ++ split cube selected ++ [cube]) ([freeCube] ++ cube :: [cube]) :=
  split_in_context [freeCube] [cube] cube selected selected_inside

/-- The general termination theorem applies to arbitrarily long lists;
these concrete aggregate increases do not weaken its conclusion. -/
theorem work_list_accessible (boxes : List (Box 3)) : Acc (WorkStep 3) boxes :=
  workStep_wellFounded.apply boxes

theorem local_split_excludes_selected : ¬ Region (split cube selected) selected := by
  intro present
  have missing := ((split_exact cube selected selected_inside selected).mp present).2
  exact missing (fun _ => Nat.le_refl _)

/-- This point violates the upward-cone test at a non-head coordinate,
so coverage must retain it in a later child rather than discard it. -/
def outsideCone : Marking 3 := fun coordinate => if coordinate = 1 then 8 else 9

theorem local_split_retains_uncovered : Region (split cube selected) outsideCone := by
  apply (split_exact cube selected selected_inside outsideCone).mpr
  constructor
  · unfold Contains cube outsideCone
    decide +kernel
  · intro above
    have impossible := above 1
    change 9 ≤ 8 at impossible
    exact Nat.not_succ_le_self 8 impossible

theorem overlap_retains_selected : Region (split cube selected ++ [cube]) selected :=
  ⟨cube, List.mem_append.mpr (.inr List.mem_cons_self), selected_inside⟩

/-- Coverage survives the same overlapping update even though the
selected point remains in the unchanged copy of the original box. -/
theorem overlapping_update_preserves_coverage :
    CoversUncovered (split freeCube selected ++ [freeCube]) [selected] := by
  have initial : CoversUncovered [freeCube, freeCube] [] := by
    intro point _
    exact ⟨freeCube, List.mem_cons_self, fun _ => True.intro⟩
  exact coversUncovered_after_replace [] [freeCube] freeCube selected [] selected_inside_free initial

def oneFree : Box 1 := fun _ => none
def oneZero : Marking 1 := fun _ => 0

/-- A selected zero coordinate produces a genuinely empty child, rather
than an off-by-one interval that accidentally retains the selected point. -/
theorem zero_cut_empty (point : Marking 1) : ¬ Contains (cut oneFree 0 0) point := by
  intro inside
  have impossible := inside 0
  rw [cut_at] at impossible
  exact Nat.not_lt_zero _ impossible

theorem zero_selected_split_empty_region : ¬ Region (split oneFree oneZero) oneZero := by
  intro present
  have missing := ((split_exact oneFree oneZero (fun _ => True.intro) oneZero).mp present).2
  exact missing (fun _ => Nat.le_refl _)

def noCoordinates : Box 0 := Fin.elim0
def emptyPoint : Marking 0 := Fin.elim0

theorem empty_dimension_split : split noCoordinates emptyPoint = [] := rfl

theorem empty_dimension_deletes : WorkStep 0 [] [noCoordinates] :=
  split_in_context [] [] noCoordinates emptyPoint (fun coordinate => Fin.elim0 coordinate)

/-- Even the zero-dimensional product contains its empty tuple. Its
upward cone is the whole product, so the local remainder is empty. -/
theorem empty_dimension_exact (point : Marking 0) :
    (∃ child ∈ split noCoordinates emptyPoint, Contains child point) ↔
      Contains noCoordinates point ∧ ¬ Below emptyPoint point :=
  split_exact noCoordinates emptyPoint (fun coordinate => Fin.elim0 coordinate) point

open FiniteListReplacement

private theorem repeated_children_smaller : ∀ child ∈ [3, 3, 3], child < (4 : Nat) := by
  intro child listed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;> decide +kernel

/-- Repeated smaller children are legitimate. The list grows from one
entry to three, and the sum grows from four to nine. -/
theorem repeated_children_step : Step Nat.lt [3, 3, 3] [4] :=
  .replace repeated_children_smaller

theorem repeated_children_in_middle : Step Nat.lt [10, 3, 3, 3, 20] [10, 4, 20] :=
  replace_in_context [10] [20] [3, 3, 3] 4 repeated_children_smaller

theorem deletion_in_middle : Step Nat.lt [10, 20] [10, 0, 20] :=
  replace_in_context [10] [20] [] 0 (fun _ impossible => False.elim (List.not_mem_nil impossible))

theorem repeated_children_terminate : Acc (Step Nat.lt) [3, 3, 3] :=
  (wellFounded Nat.lt_wfRel.wf).apply _

end Thesis.Causality.Examples.CoordinateBoxes
