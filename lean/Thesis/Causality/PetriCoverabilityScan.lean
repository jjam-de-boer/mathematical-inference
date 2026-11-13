import Thesis.Causality.PetriCoverability

namespace Thesis.Causality.PetriNet

open CoordinateBoxes

/-!
# Finite witnessed scans for backward coverability

Each scan traverses explicitly supplied finite data. Coordinate comparisons
use natural decidability. Basis coverage returns an actual stored entry,
which can be lifted to the requested source without choosing a witness
from a proposition. Predecessor selection checks the whole current basis
against its finite transition family and retains the selected entry and
transition as data. Failure proves saturation of that current basis.

The nested predecessor scan does not materialize a basis-by-transition
product, impose a token or word cutoff, or iterate basis updates. These
finite scans are not yet a recursive saturated-basis construction or a
general coverability solver. Boxes are located by the independent
`CoordinateBoxScan` module; no box is discarded here.
-/

variable {places transitions : Nat}
variable {net : Thesis.Causality.PetriNet places transitions} {target : Marking places}

def markingBelow (lower upper : Marking places) : Bool :=
  (List.finRange places).all (fun place => decide (lower place ≤ upper place))

theorem markingBelow_exact (lower upper : Marking places) :
    markingBelow lower upper = true ↔ Below lower upper := by
  simp only [markingBelow, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro every place
    exact every place (List.mem_finRange place)
  · intro every place _
    exact every place

structure CoverageHit (entries : List (CoverabilityWitness net target)) (before : Marking places) where
  entry : CoverabilityWitness net target
  listed : entry ∈ entries
  enough : Below entry.source before

/-- Produce the actual covering execution at the requested source. The
stored suffix is lifted with its exact computed endpoint and surplus. -/
def CoverageHit.witness {entries : List (CoverabilityWitness net target)} {before : Marking places}
    (hit : CoverageHit entries before) : CoverabilityWitness net target :=
  hit.entry.lift before hit.enough

theorem CoverageHit.covered {entries : List (CoverabilityWitness net target)} {before : Marking places}
    (hit : CoverageHit entries before) : Covered (entries.map (fun entry => entry.source)) before :=
  ⟨hit.entry.source, List.mem_map_of_mem hit.listed, hit.enough⟩

private def CoverageHit.prepend (head : CoverabilityWitness net target)
    {entries : List (CoverabilityWitness net target)} {before : Marking places}
    (hit : CoverageHit entries before) : CoverageHit (head :: entries) before where
  entry := hit.entry
  listed := List.mem_cons_of_mem head hit.listed
  enough := hit.enough

def scanCoverage : (entries : List (CoverabilityWitness net target)) → (before : Marking places) →
    Option (CoverageHit entries before)
  | [], _ => none
  | head :: tail, before =>
      if enough : markingBelow head.source before = true then
        some ⟨head, List.mem_cons_self, (markingBelow_exact head.source before).mp enough⟩
      else (scanCoverage tail before).map (fun hit => hit.prepend head)

theorem scanCoverage_none_iff (entries : List (CoverabilityWitness net target)) (before : Marking places) :
    scanCoverage entries before = none ↔ ¬ Covered (entries.map (fun entry => entry.source)) before := by
  induction entries with
  | nil =>
      constructor
      · rintro _ ⟨point, impossible, _⟩
        exact List.not_mem_nil impossible
      · intro _
        rfl
  | cons head tail ih =>
      unfold scanCoverage
      split
      · next enough =>
          constructor
          · intro impossible
            cases impossible
          · intro missing
            exact False.elim (missing
              ⟨head.source, List.mem_cons_self, (markingBelow_exact head.source before).mp enough⟩)
      · next short =>
          rw [Option.map_eq_none_iff, ih]
          constructor
          · rintro missing ⟨point, listed, enough⟩
            rcases List.mem_cons.mp listed with equal | listed
            · subst point
              exact short ((markingBelow_exact head.source before).mpr enough)
            · exact missing ⟨point, listed, enough⟩
          · rintro missing ⟨point, listed, enough⟩
            exact missing ⟨point, List.mem_cons_of_mem head.source listed, enough⟩

theorem scanCoverage_found_iff (entries : List (CoverabilityWitness net target)) (before : Marking places) :
    (scanCoverage entries before).isSome = true ↔ Covered (entries.map (fun entry => entry.source)) before := by
  constructor
  · intro found
    cases computed : scanCoverage entries before with
    | none => rw [computed] at found; cases found
    | some hit => exact hit.covered
  · intro covered
    cases computed : scanCoverage entries before with
    | none => exact False.elim (((scanCoverage_none_iff entries before).mp computed) covered)
    | some hit => rfl

/-- A fresh candidate retains its actual old entry and transition.
The new witness is computed by `prepend`; no runtime data are extracted
from the negation of the saturation proposition. -/
structure FreshPredecessor (entries : List (CoverabilityWitness net target)) where
  entry : CoverabilityWitness net target
  listed : entry ∈ entries
  transition : Fin transitions
  uncovered : ¬ Covered (entries.map (fun entry => entry.source)) (net.predecessor transition entry.source)

def FreshPredecessor.witness {entries : List (CoverabilityWitness net target)}
    (hit : FreshPredecessor entries) : CoverabilityWitness net target :=
  hit.entry.prepend hit.transition

/-- Check a finite transition suffix for one fixed basis entry. The basis
used for coverage remains the whole supplied list, not the unscanned suffix. -/
private def scanTransitions (entries : List (CoverabilityWitness net target))
    (entry : CoverabilityWitness net target) (listed : entry ∈ entries) :
    List (Fin transitions) → Option (FreshPredecessor entries)
  | [] => none
  | transition :: rest =>
      match checked : scanCoverage entries (net.predecessor transition entry.source) with
      | some _ => scanTransitions entries entry listed rest
      | none => some ⟨entry, listed, transition, (scanCoverage_none_iff _ _).mp checked⟩

private theorem scanTransitions_none_iff (entries : List (CoverabilityWitness net target))
    (entry : CoverabilityWitness net target) (listed : entry ∈ entries) (remaining : List (Fin transitions)) :
    scanTransitions entries entry listed remaining = none ↔
      ∀ transition ∈ remaining, Covered (entries.map (fun entry => entry.source))
        (net.predecessor transition entry.source) := by
  induction remaining with
  | nil =>
      constructor
      · intro _ transition impossible
        exact False.elim (List.not_mem_nil impossible)
      · intro _
        rfl
  | cons transition rest ih =>
      unfold scanTransitions
      split
      · next hit checked =>
          rw [ih]
          constructor
          · intro every other present
            rcases List.mem_cons.mp present with equal | present
            · subst other
              exact hit.covered
            · exact every other present
          · intro every other present
            exact every other (List.mem_cons_of_mem transition present)
      · next checked =>
          constructor
          · intro impossible
            cases impossible
          · intro every
            exact False.elim (((scanCoverage_none_iff _ _).mp checked)
              (every transition List.mem_cons_self))

/-- Walk the basis without constructing a list of all entry/transition
pairs. The inclusion argument is proof-only and records which actual
entries the remaining suffix borrows from the full current basis. -/
private def scanEntries (entries : List (CoverabilityWitness net target)) :
    (remaining : List (CoverabilityWitness net target)) →
    (∀ entry ∈ remaining, entry ∈ entries) → Option (FreshPredecessor entries)
  | [], _ => none
  | entry :: rest, included =>
      match scanTransitions entries entry (included entry List.mem_cons_self) (List.finRange transitions) with
      | some hit => some hit
      | none => scanEntries entries rest
          (fun other listed => included other (List.mem_cons_of_mem entry listed))

private theorem scanEntries_none_iff (entries : List (CoverabilityWitness net target))
    (remaining : List (CoverabilityWitness net target)) :
    ∀ included : (∀ entry ∈ remaining, entry ∈ entries),
      scanEntries entries remaining included = none ↔
        ∀ entry ∈ remaining, ∀ transition, Covered (entries.map (fun entry => entry.source))
          (net.predecessor transition entry.source) := by
  induction remaining with
  | nil =>
      intro included
      constructor
      · intro _ entry impossible
        exact False.elim (List.not_mem_nil impossible)
      · intro _
        rfl
  | cons entry rest ih =>
      intro included
      unfold scanEntries
      cases checked : scanTransitions entries entry (included entry List.mem_cons_self)
          (List.finRange transitions) with
      | some hit =>
          constructor
          · intro impossible
            cases impossible
          · intro every
            have impossible := (scanTransitions_none_iff entries entry
              (included entry List.mem_cons_self) (List.finRange transitions)).mpr
                (fun transition _ => every entry List.mem_cons_self transition)
            rw [checked] at impossible
            cases impossible
      | none =>
          rw [ih]
          constructor
          · intro every other present transition
            rcases List.mem_cons.mp present with equal | present
            · subst other
              exact ((scanTransitions_none_iff entries entry
                (included entry List.mem_cons_self) (List.finRange transitions)).mp checked)
                  transition (List.mem_finRange transition)
            · exact every other present transition
          · intro every other present transition
            exact every other (List.mem_cons_of_mem entry present) transition

def scanFreshPredecessor (entries : List (CoverabilityWitness net target)) :
    Option (FreshPredecessor entries) :=
  scanEntries entries entries (fun _ listed => listed)

/-- Failure means closure under every actual finite transition index.
It does not mean absence below a cutoff, nor absence only inside one box. -/
theorem scanFreshPredecessor_none_iff (entries : List (CoverabilityWitness net target)) :
    scanFreshPredecessor entries = none ↔ Saturated net (entries.map (fun entry => entry.source)) := by
  unfold scanFreshPredecessor
  rw [scanEntries_none_iff]
  constructor
  · intro every point listed transition
    obtain ⟨entry, entryListed, equal⟩ := List.mem_map.mp listed
    subst point
    exact every entry entryListed transition
  · intro closed entry listed transition
    exact closed entry.source (List.mem_map_of_mem listed) transition

theorem scanFreshPredecessor_found_iff (entries : List (CoverabilityWitness net target)) :
    (scanFreshPredecessor entries).isSome = true ↔ ¬ Saturated net (entries.map (fun entry => entry.source)) := by
  constructor
  · intro found closed
    cases checked : scanFreshPredecessor entries with
    | none => rw [checked] at found; cases found
    | some hit => exact hit.uncovered (closed hit.entry.source (List.mem_map_of_mem hit.listed) hit.transition)
  · intro notClosed
    cases checked : scanFreshPredecessor entries with
    | none => exact False.elim (notClosed ((scanFreshPredecessor_none_iff entries).mp checked))
    | some hit => rfl

end Thesis.Causality.PetriNet
