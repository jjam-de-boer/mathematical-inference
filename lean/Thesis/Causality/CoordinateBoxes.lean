import Thesis.Causality.FiniteListReplacement
import Thesis.Causality.PetriNet

namespace Thesis.Causality.CoordinateBoxes

open PetriNet

/-!
# Finite coordinate boxes as a constructive termination measure

A box gives each natural coordinate either a strict finite upper bound
or no upper bound. If a selected point belongs to a box, removing its
upward cone splits that box into finitely many boxes: child i imposes the
new bound xᵢ < selectedᵢ and retains every other bound. The children may
overlap and may be empty. Their union is exactly the local remainder.

Each child strictly lowers the lexicographic pair consisting of the
number of unbounded coordinates and the sum of finite bounds. Replacing
one work-list entry by these children is therefore well-founded, even
though list length and aggregate rank sums can increase.

The global coverage invariant is deliberately one-sided. Other boxes
may overlap the selected box and retain already covered points. We prove
that every point outside the growing basis's upward closure is still in
some remaining box; we do not assert global equality with that complement.

These are termination and coverage foundations only. No backward search,
saturation procedure, Petri pumping test or reachability solver is defined.
-/

/-- `some cap` means a strict bound; `none` imposes no restriction.
In particular, a zero bound describes an empty box. -/
abbrev Box (dimension : Nat) := Fin dimension → Option Nat

variable {dimension : Nat}

def Contains (box : Box dimension) (point : Marking dimension) : Prop :=
  ∀ coordinate, match box coordinate with
    | none => True
    | some cap => point coordinate < cap

/-- Replace one coordinate's bound, retaining the other literal bounds. -/
def cut (box : Box dimension) (coordinate : Fin dimension) (bound : Nat) : Box dimension :=
  fun other => if other = coordinate then some bound else box other

theorem cut_at (box : Box dimension) (coordinate : Fin dimension) (bound : Nat) :
    cut box coordinate bound coordinate = some bound := if_pos rfl

theorem cut_away (box : Box dimension) {coordinate other : Fin dimension}
    (bound : Nat) (different : other ≠ coordinate) :
    cut box coordinate bound other = box other := if_neg different

/-- Enumerating all coordinates retains empty and duplicate children;
neither pruning nor deciding equality of box functions is necessary. -/
def split (box : Box dimension) (selected : Marking dimension) : List (Box dimension) :=
  (List.finRange dimension).map (fun coordinate => cut box coordinate (selected coordinate))

theorem cut_mem_split (box : Box dimension) (selected : Marking dimension)
    (coordinate : Fin dimension) :
    cut box coordinate (selected coordinate) ∈ split box selected :=
  List.mem_map_of_mem (List.mem_finRange coordinate)

/-- Find an actually violating coordinate by finite recursion. This uses
only decidable natural comparisons, not choice from a negated universal. -/
def violatingCoordinate : {dimension : Nat} → (lower upper : Marking dimension) →
    (¬ Below lower upper) → {coordinate : Fin dimension // upper coordinate < lower coordinate}
  | 0, _, _, missing => False.elim (missing (fun coordinate => Fin.elim0 coordinate))
  | n + 1, lower, upper, missing =>
      if first : upper 0 < lower 0 then ⟨0, first⟩ else
        let tailMissing : ¬ Below (fun i : Fin n => lower i.succ) (fun i => upper i.succ) := by
          intro tailBelow
          apply missing
          intro coordinate
          refine Fin.cases ?_ (fun i => tailBelow i) coordinate
          exact Nat.le_of_not_gt first
        let found := violatingCoordinate (fun i : Fin n => lower i.succ)
          (fun i => upper i.succ) tailMissing
        ⟨found.val.succ, found.property⟩

/-- Exact removal of the upward cone *inside this one box*. The selected
point must belong to the parent, so each new cap really refines that box. -/
theorem split_exact (box : Box dimension) (selected : Marking dimension)
    (inside : Contains box selected) (point : Marking dimension) :
    (∃ child ∈ split box selected, Contains child point) ↔
      Contains box point ∧ ¬ Below selected point := by
  constructor
  · rintro ⟨child, listed, contains⟩
    obtain ⟨coordinate, _, equal⟩ := List.mem_map.mp listed
    subst child
    have strict : point coordinate < selected coordinate := by
      have bound := contains coordinate
      rw [cut_at] at bound
      exact bound
    constructor
    · intro other
      by_cases same : other = coordinate
      · subst other
        have original := inside coordinate
        cases cap : box coordinate with
        | none => trivial
        | some bound =>
            rw [cap] at original
            exact Nat.lt_trans strict original
      · have original := contains other
        rw [cut_away box _ same] at original
        exact original
    · intro above
      exact Nat.not_lt_of_ge (above coordinate) strict
  · rintro ⟨original, missing⟩
    let found := violatingCoordinate selected point missing
    refine ⟨cut box found.val (selected found.val), cut_mem_split box selected found.val, ?_⟩
    intro other
    by_cases same : other = found.val
    · subst other
      rw [cut_at]
      exact found.property
    · rw [cut_away box _ same]
      exact original other

/-- Accumulate one coordinate's contribution to the two-part rank.
The second component is not used to compare boxes with different first
components: bounding a previously free coordinate may increase it greatly. -/
def addRank : Option Nat → Nat × Nat → Nat × Nat
  | none, (free, budget) => (free + 1, budget)
  | some cap, (free, budget) => (free, budget + cap)

/-- Number of unbounded coordinates, followed by the sum of finite caps.
Recursion on dimension avoids any equality test on whole box functions. -/
def rank : {dimension : Nat} → Box dimension → Nat × Nat
  | 0, _ => (0, 0)
  | n + 1, box => addRank (box 0) (rank (fun i : Fin n => box i.succ))

def RankBelow (child parent : Box dimension) : Prop :=
  Prod.Lex Nat.lt Nat.lt (rank child) (rank parent)

theorem rankBelow_wellFounded : WellFounded (@RankBelow dimension) :=
  InvImage.wf rank (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

private theorem addRank_strict (cap : Option Nat) {child parent : Nat × Nat}
    (strict : Prod.Lex Nat.lt Nat.lt child parent) :
    Prod.Lex Nat.lt Nat.lt (addRank cap child) (addRank cap parent) := by
  cases strict with
  | left leftBudget rightBudget smaller =>
      cases cap with
      | none => exact .left _ _ (Nat.add_lt_add_right smaller 1)
      | some bound => exact .left _ _ smaller
  | right free smaller =>
      cases cap with
      | none => exact .right _ smaller
      | some bound => exact .right _ (Nat.add_lt_add_right smaller bound)

/-- One child strictly decreases rank. In the free-coordinate case it
is the first component that decreases; otherwise it is the finite cap sum.
Containment is essential for the latter decrease. -/
theorem cut_rank_lt (box : Box dimension) (selected : Marking dimension)
    (inside : Contains box selected) (coordinate : Fin dimension) :
    RankBelow (cut box coordinate (selected coordinate)) box := by
  induction dimension with
  | zero => exact Fin.elim0 coordinate
  | succ n ih =>
      refine Fin.cases ?_ (fun i => ?_) coordinate
      · have tailEqual : (fun i : Fin n => cut box 0 (selected 0) i.succ) =
            (fun i : Fin n => box i.succ) := by
          funext i
          exact cut_away box _ (Fin.succ_ne_zero i)
        unfold RankBelow
        rw [rank, cut_at, tailEqual]
        change Prod.Lex Nat.lt Nat.lt
          (addRank (some (selected 0)) (rank (fun i : Fin n => box i.succ)))
          (addRank (box 0) (rank (fun i : Fin n => box i.succ)))
        cases cap : box 0 with
        | none => exact .left _ _ (Nat.lt_succ_self _)
        | some bound =>
            have strict := inside 0
            rw [cap] at strict
            exact .right _ (Nat.add_lt_add_left strict _)
      · have headEqual : cut box i.succ (selected i.succ) 0 = box 0 :=
          cut_away box _ (Fin.succ_ne_zero i).symm
        have tailEqual : (fun j : Fin n => cut box i.succ (selected i.succ) j.succ) =
            cut (fun j : Fin n => box j.succ) i (selected i.succ) := by
          funext j
          simp only [cut, Fin.succ_inj]
        have tailInside : Contains (fun j : Fin n => box j.succ) (fun j => selected j.succ) :=
          fun j => inside j.succ
        have strict := ih (fun j : Fin n => box j.succ) (fun j => selected j.succ) tailInside i
        unfold RankBelow at strict ⊢
        rw [rank, rank, headEqual, tailEqual]
        exact addRank_strict (box 0) strict

theorem split_rank_lt (box : Box dimension) (selected : Marking dimension)
    (inside : Contains box selected) {child : Box dimension} (listed : child ∈ split box selected) :
    RankBelow child box := by
  obtain ⟨coordinate, _, equal⟩ := List.mem_map.mp listed
  subst child
  exact cut_rank_lt box selected inside coordinate

/-- Relation orientation is new list before old list, as required for
well-founded recursion. Only one literal occurrence is replaced at a time. -/
abbrev WorkStep (dimension : Nat) :=
  FiniteListReplacement.Step (@RankBelow dimension)

theorem workStep_wellFounded : WellFounded (WorkStep dimension) :=
  FiniteListReplacement.wellFounded rankBelow_wellFounded

theorem split_in_context (before after : List (Box dimension)) (box : Box dimension)
    (selected : Marking dimension) (inside : Contains box selected) :
    WorkStep dimension (before ++ split box selected ++ after) (before ++ box :: after) :=
  FiniteListReplacement.replace_in_context before after _ box
    (fun _ listed => split_rank_lt box selected inside listed)

/-- Union of the work-list boxes. Overlap and duplicate boxes are allowed. -/
def Region (boxes : List (Box dimension)) (point : Marking dimension) : Prop :=
  ∃ box ∈ boxes, Contains box point

/-- Upward closure of the supplied basis, independent of the work list. -/
def Covered (basis : List (Marking dimension)) (point : Marking dimension) : Prop :=
  ∃ selected ∈ basis, Below selected point

/-- The work list contains every point not yet covered by the basis.
It may also contain covered points; no pairwise disjointness is required. -/
def CoversUncovered (boxes : List (Box dimension)) (basis : List (Marking dimension)) : Prop :=
  ∀ point, ¬ Covered basis point → Region boxes point

/-- Replace just the selected occurrence. An old region witness in an
unchanged box survives literally; a witness in the replaced box is routed
to one of its children by the exact local split theorem. -/
theorem region_after_replace (before after : List (Box dimension)) (box : Box dimension)
    (selected : Marking dimension) (inside : Contains box selected)
    (point : Marking dimension) (present : Region (before ++ box :: after) point)
    (uncovered : ¬ Below selected point) :
    Region (before ++ split box selected ++ after) point := by
  rcases present with ⟨old, listed, contains⟩
  rcases List.mem_append.mp listed with first | remaining
  · exact ⟨old, List.mem_append.mpr (.inl (List.mem_append.mpr (.inl first))), contains⟩
  · rcases List.mem_cons.mp remaining with same | last
    · subst old
      obtain ⟨child, listed, contains⟩ := (split_exact box selected inside point).mpr ⟨contains, uncovered⟩
      exact ⟨child, List.mem_append.mpr (.inl (List.mem_append.mpr (.inr listed))), contains⟩
    · exact ⟨old, List.mem_append.mpr (.inr last), contains⟩

/-- Adding the selected point to the basis and splitting one containing
box preserves coverage of every still-uncovered point. Other overlapping
boxes need not be split, which is why the invariant is an inclusion. -/
theorem coversUncovered_after_replace (before after : List (Box dimension))
    (box : Box dimension) (selected : Marking dimension) (basis : List (Marking dimension))
    (inside : Contains box selected)
    (coverage : CoversUncovered (before ++ box :: after) basis) :
    CoversUncovered (before ++ split box selected ++ after) (selected :: basis) := by
  intro point missing
  have oldMissing : ¬ Covered basis point := by
    rintro ⟨old, listed, below⟩
    exact missing ⟨old, List.mem_cons_of_mem selected listed, below⟩
  have newMissing : ¬ Below selected point := by
    intro below
    exact missing ⟨selected, List.mem_cons_self, below⟩
  exact region_after_replace before after box selected inside point (coverage point oldMissing) newMissing

/-- A single entirely unbounded box initializes the coverage invariant
for any basis, in particular for the empty basis before a search starts. -/
theorem unbounded_covers (basis : List (Marking dimension)) :
    CoversUncovered [fun _ => none] basis := by
  intro point _
  exact ⟨fun _ => none, List.mem_cons_self, fun _ => True.intro⟩

end Thesis.Causality.CoordinateBoxes
