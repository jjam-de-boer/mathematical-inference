import Thesis.Causality.CoordinateBoxes

namespace Thesis.Causality.CoordinateBoxes

open PetriNet

/-!
# Finite checks and literal locations for coordinate boxes

Box membership checks every finite coordinate. An absent upper bound is
always satisfied; a finite bound remains strict, including an empty bound
of zero. The scan returns the first containing occurrence, together with
its actual preceding and following lists. Thus a later replacement can use
the literal context required by the well-founded work-list relation.

No equality decision on box functions is used. A successful location stores
data and proofs directly from the finite traversal; it is not selected from
a propositional existence assertion. Failure means absence from the whole
supplied region, including for an empty list or zero coordinates.

This module does not discard boxes, select predecessors, or iterate a
coverability search. In particular, membership failure for one point does
not justify deleting the box for future points.
-/

variable {dimension : Nat}

def contains (box : Box dimension) (point : Marking dimension) : Bool :=
  (List.finRange dimension).all fun coordinate =>
    match box coordinate with
    | none => true
    | some cap => decide (point coordinate < cap)

theorem contains_exact (box : Box dimension) (point : Marking dimension) :
    contains box point = true ↔ Contains box point := by
  rw [contains, List.all_eq_true]
  constructor
  · intro every coordinate
    have checked := every coordinate (List.mem_finRange coordinate)
    cases bound : box coordinate with
    | none => trivial
    | some cap =>
        rw [bound] at checked
        exact of_decide_eq_true checked
  · intro every coordinate _
    have bound := every coordinate
    cases cap : box coordinate with
    | none => rfl
    | some maximum =>
        rw [cap] at bound
        exact decide_eq_true bound

/-- One actual occurrence, retaining the order of both surrounding lists.
Duplicate and overlapping boxes therefore cause no ambiguity of identity. -/
structure BoxLocation (boxes : List (Box dimension)) (point : Marking dimension) where
  before : List (Box dimension)
  box : Box dimension
  after : List (Box dimension)
  reconstruct : boxes = before ++ box :: after
  inside : Contains box point

private def BoxLocation.prepend (head : Box dimension) {boxes : List (Box dimension)}
    {point : Marking dimension} (location : BoxLocation boxes point) : BoxLocation (head :: boxes) point where
  before := head :: location.before
  box := location.box
  after := location.after
  reconstruct := congrArg (List.cons head) location.reconstruct
  inside := location.inside

theorem BoxLocation.present {boxes : List (Box dimension)} {point : Marking dimension}
    (location : BoxLocation boxes point) : Region boxes point := by
  refine ⟨location.box, ?_, location.inside⟩
  exact Eq.mpr (congrArg (fun items => location.box ∈ items) location.reconstruct)
    (List.mem_append.mpr (.inr List.mem_cons_self))

def locateBox : (boxes : List (Box dimension)) → (point : Marking dimension) →
    Option (BoxLocation boxes point)
  | [], _ => none
  | head :: tail, point =>
      if inside : contains head point = true then
        some ⟨[], head, tail, rfl, (contains_exact head point).mp inside⟩
      else (locateBox tail point).map (fun location => location.prepend head)

/-- Failure excludes every occurrence in the supplied list, not only the
first tested box. All disjunction cases below come from finite list data. -/
theorem locateBox_none_iff (boxes : List (Box dimension)) (point : Marking dimension) :
    locateBox boxes point = none ↔ ¬ Region boxes point := by
  induction boxes with
  | nil =>
      constructor
      · rintro _ ⟨box, impossible, _⟩
        exact List.not_mem_nil impossible
      · intro _
        rfl
  | cons head tail ih =>
      unfold locateBox
      split
      · next inside =>
          constructor
          · intro impossible
            cases impossible
          · intro missing
            exact False.elim (missing ⟨head, List.mem_cons_self, (contains_exact head point).mp inside⟩)
      · next outside =>
          rw [Option.map_eq_none_iff, ih]
          constructor
          · rintro missing ⟨box, listed, inside⟩
            rcases List.mem_cons.mp listed with equal | listed
            · subst box
              exact outside ((contains_exact head point).mpr inside)
            · exact missing ⟨box, listed, inside⟩
          · intro missing present
            rcases present with ⟨box, listed, inside⟩
            exact missing ⟨box, List.mem_cons_of_mem head listed, inside⟩

theorem locateBox_found_iff (boxes : List (Box dimension)) (point : Marking dimension) :
    (locateBox boxes point).isSome = true ↔ Region boxes point := by
  constructor
  · intro found
    cases computed : locateBox boxes point with
    | none => rw [computed] at found; cases found
    | some location => exact location.present
  · intro present
    cases computed : locateBox boxes point with
    | none => exact False.elim (((locateBox_none_iff boxes point).mp computed) present)
    | some location => rfl

end Thesis.Causality.CoordinateBoxes
