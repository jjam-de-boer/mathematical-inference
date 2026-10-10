import Thesis.CausalTransport.ActivePathBoundary

namespace Thesis
namespace Causality

universe u

open PathSpecification

variable {S : ObservedSignature.{u}} {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}

/-!
# A noncollider path head has exactly one actual outgoing observed input

Whole head-phase conservation does not identify which rows a coordinate
connects.  A selected internal noncollider has one incoming and one outgoing
path arrow.  Simplicity fixes its two neighbours, the actual head classifier
supplies an incoming arrow, and the noncollider classifier excludes two
incoming arrows.  Real adjacency supplies the other outgoing arrow; strict
DAG rank excludes its reversal.  That outgoing neighbour must be observed,
because an observed-to-latent arrow is impossible in the expanded graph.

The result below describes the complete original path-parent column, not just
an odd fold of possible reads.  Additional ambient parents and children have
no path incidence.  The two window orientations are both allowed: this is a
chain head, not the source-side exit choice of an omitted two-output fork.

Observed endpoints are handled separately.  A selected endpoint has only an
incoming incident arrow and consequently no outgoing path-parent read.  Its
own observed coordinate has one selected-row incidence, rather than a falsely
invented chain continuation.  An omitted nonsingleton endpoint instead has
one genuine outgoing observed receiver, but no selected own row.  The two
endpoint orientations are both classified without contracting latent edges.
These graph-only theorems retain the original
signature universe and consume window existentials in Prop only.  They never
choose data from a mere existence proposition.
-/

namespace ActivePathInput

/-- The two actual neighbours exhaust every outgoing observed path read
of an internal coordinate.  An arrow in the ambient graph is irrelevant
unless its receiver is one of those two literal consecutive neighbours. -/
theorem incomingEdge_internal_window_iff (path : ActivePath graph m given (.observed source) (.observed target))
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (parent row : Fin S.count)
    (window : path.nodes = before ++ previous :: .observed parent :: next :: after) :
    incomingEdge graph m path.nodes (.observed parent) row = true ↔
      (.observed row = previous ∧ graph.expandedMutilatedEdge m (.observed parent) previous = true) ∨
      (.observed row = next ∧ graph.expandedMutilatedEdge m (.observed parent) next = true) := by
  constructor
  · intro read
    have entries := Bool.and_eq_true_iff.mp read
    rw [stepOnPath_symm] at entries
    rcases (stepOnPath_internal_window path.simple before after previous (.observed parent) next (.observed row) window).mp
      entries.1 with atPrevious | atNext
    · exact Or.inl ⟨atPrevious, by simpa only [atPrevious] using entries.2⟩
    · exact Or.inr ⟨atNext, by simpa only [atNext] using entries.2⟩
  · intro neighbor
    apply Bool.and_eq_true_iff.mpr
    rcases neighbor with ⟨atPrevious, arrow⟩ | ⟨atNext, arrow⟩
    · refine ⟨?_, ?_⟩
      · rw [stepOnPath_symm]
        exact (stepOnPath_internal_window path.simple before after _ _ _ _ window).mpr (Or.inl atPrevious)
      · rw [atPrevious]; exact arrow
    · refine ⟨?_, ?_⟩
      · rw [stepOnPath_symm]
        exact (stepOnPath_internal_window path.simple before after _ _ _ _ window).mpr (Or.inr atNext)
      · rw [atNext]; exact arrow

-- An actual incoming arrow forbids its reverse.  This uses the expanded
-- graph's proved strict DAG rank, not a decidability assumption on reachability.
private theorem reverse_arrow_absent (left right : SeparationNode S)
    (incoming : graph.expandedMutilatedEdge m left right = true) :
    graph.expandedMutilatedEdge m right left = false := by
  apply Bool.eq_false_iff.mpr
  intro reverse
  exact Nat.lt_asymm (graph.expandedMutilatedEdge_rank_lt m incoming)
    (graph.expandedMutilatedEdge_rank_lt m reverse)

/-- An actual internal head which is not a collider has one and only one
observed outgoing receiver.  The complete parent-input function is its
receiver indicator; the receiver is not supplied by an independent flag. -/
theorem head_internal_unique_input (path : ActivePath graph m given (.observed source) (.observed target))
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (parent : Fin S.count)
    (window : path.nodes = before ++ previous :: .observed parent :: next :: after)
    (head : headRows graph m path.nodes parent = true)
    (noncollider : colliderRows graph m path.nodes parent = false) :
    Exists fun child : Fin S.count => forall row,
      incomingEdge graph m path.nodes (.observed parent) row = decide (row = child) := by
  have incoming := head
  rw [headRows_internal_window path.simple before after previous next parent window, Bool.or_eq_true_iff] at incoming
  have classifier := noncollider
  rw [colliderRows_internal_window path.simple before after previous next parent window] at classifier
  change (graph.expandedMutilatedEdge m previous (.observed parent) &&
    graph.expandedMutilatedEdge m next (.observed parent)) = false at classifier
  have first := Consecutive.pair_of_append before (next :: after) previous (.observed parent) (window ▸ path.adjacent)
  have second := Consecutive.pair_of_append (relation := Adjacent graph m) (before ++ [previous]) after
    (.observed parent) next (by simpa only [List.append_assoc, List.singleton_append] using window ▸ path.adjacent)
  rcases incoming with fromPrevious | fromNext
  · have notNext : graph.expandedMutilatedEdge m next (.observed parent) = false := by
      apply Bool.eq_false_iff.mpr
      intro arrow
      rw [fromPrevious, arrow] at classifier
      cases classifier
    have toNext : graph.expandedMutilatedEdge m (.observed parent) next = true := by
      rcases second with arrow | backward
      · exact arrow
      · rw [notNext] at backward; cases backward
    have notPrevious := reverse_arrow_absent previous (.observed parent) fromPrevious
    cases next with
    | latentPair _ _ => exact False.elim (Bool.false_ne_true toNext)
    | observed child =>
        refine ⟨child, ?_⟩
        intro row
        apply Bool.eq_iff_iff.mpr
        rw [incomingEdge_internal_window_iff path before after previous (.observed child) parent row window, decide_eq_true_eq]
        constructor
        · rintro (⟨_same, arrow⟩ | ⟨same, _arrow⟩)
          · rw [notPrevious] at arrow; cases arrow
          · exact SeparationNode.observed.inj same
        · intro same
          subst row
          exact Or.inr ⟨rfl, toNext⟩
  · have notPrevious : graph.expandedMutilatedEdge m previous (.observed parent) = false := by
      apply Bool.eq_false_iff.mpr
      intro arrow
      rw [arrow, fromNext] at classifier
      cases classifier
    have toPrevious : graph.expandedMutilatedEdge m (.observed parent) previous = true := by
      rcases first with backward | arrow
      · rw [notPrevious] at backward; cases backward
      · exact arrow
    have notNext := reverse_arrow_absent next (.observed parent) fromNext
    cases previous with
    | latentPair _ _ => exact False.elim (Bool.false_ne_true toPrevious)
    | observed child =>
        refine ⟨child, ?_⟩
        intro row
        apply Bool.eq_iff_iff.mpr
        rw [incomingEdge_internal_window_iff path before after (.observed child) next parent row window, decide_eq_true_eq]
        constructor
        · rintro (⟨same, _arrow⟩ | ⟨_same, arrow⟩)
          · exact SeparationNode.observed.inj same
          · rw [notNext] at arrow; cases arrow
        · intro same
          subst row
          exact Or.inl ⟨rfl, toPrevious⟩

/-- For any actual internal noncollider head, membership and endpoint
exclusion derive its window before deriving the unique input.  This is the
interface for callers which have only the actual selected path coordinate. -/
theorem head_unique_input_of_internal (path : ActivePath graph m given (.observed source) (.observed target))
    (parent : Fin S.count) (head : headRows graph m path.nodes parent = true)
    (noncollider : colliderRows graph m path.nodes parent = false)
    (notSource : parent ≠ source) (notTarget : parent ≠ target) :
    Exists fun child : Fin S.count => forall row,
      incomingEdge graph m path.nodes (.observed parent) row = decide (row = child) := by
  rcases exists_internal_neighbors_of_mem path.starts path.finishes (headRows_member head)
    (fun same => notSource (SeparationNode.observed.inj same))
    (fun same => notTarget (SeparationNode.observed.inj same)) with ⟨before, previous, next, after, window⟩
  exact head_internal_unique_input path before after previous next parent window head noncollider

/-- A selected first observed endpoint has no outgoing path-parent input.
Its sole incident arrow points inward, and simplicity admits no other path
receiver even if more outgoing arrows exist in the ambient graph. -/
theorem source_head_parent_absent (path : ActivePath graph m given (.observed source) (.observed target))
    (head : headRows graph m path.nodes source = true) (row : Fin S.count) :
    incomingEdge graph m path.nodes (.observed source) row = false := by
  cases shape : path.nodes with
  | nil => have impossible := path.starts; rw [shape] at impossible; cases impossible
  | cons first tail =>
      have start := path.starts
      rw [shape, List.head?_cons] at start
      have same := Option.some.inj start
      subst first
      cases tail with
      | nil => rfl
      | cons next rest =>
          have inward := head
          rw [shape, headRows_first_pair graph m source next rest (shape ▸ path.simple)] at inward
          apply Bool.eq_false_iff.mpr
          intro read
          have parts := Bool.and_eq_true_iff.mp read
          have step := parts.1
          rw [stepOnPath_symm] at step
          have receiver := (stepOnPath_first_pair (.observed source) next (.observed row) rest (shape ▸ path.simple)).mp step
          have outward := parts.2
          rw [receiver] at outward
          exact Nat.lt_asymm (graph.expandedMutilatedEdge_rank_lt m inward)
            (graph.expandedMutilatedEdge_rank_lt m outward)

/-- The same one-incidence endpoint fact holds at the actual target.
Reversal preserves consecutive input tests and the selected-head mask; it
does not replace the last neighbour by a separately chosen observation. -/
theorem target_head_parent_absent (path : ActivePath graph m given (.observed source) (.observed target))
    (head : headRows graph m path.nodes target = true) (row : Fin S.count) :
    incomingEdge graph m path.nodes (.observed target) row = false := by
  have reversedHead : headRows graph m path.reverse.nodes target = true := by
    change headRows graph m path.nodes.reverse target = true
    simpa only [headRows, incomingEdge, stepOnPath_reverse, List.any_reverse] using head
  have absent := source_head_parent_absent path.reverse reversedHead row
  change incomingEdge graph m path.nodes.reverse (.observed target) row = false at absent
  simpa only [incomingEdge, stepOnPath_reverse] using absent

/-- An omitted first endpoint of a nonsingleton path instead has exactly
one outgoing observed receiver.  Unlike an internal fork it does not have
two outgoing neighbours, and its own row is not selected by the head scan. -/
theorem source_nonhead_unique_input (path : ActivePath graph m given (.observed source) (.observed target))
    (distinct : source ≠ target) (head : headRows graph m path.nodes source = false) :
    Exists fun child : Fin S.count => forall row,
      incomingEdge graph m path.nodes (.observed source) row = decide (row = child) := by
  cases shape : path.nodes with
  | nil => have impossible := path.starts; rw [shape] at impossible; cases impossible
  | cons first tail =>
      have start := path.starts
      rw [shape, List.head?_cons] at start
      have same := Option.some.inj start
      subst first
      cases tail with
      | nil =>
          have finish := path.finishes
          rw [shape, List.getLast?_singleton] at finish
          exact False.elim (distinct (SeparationNode.observed.inj (Option.some.inj finish)))
      | cons next rest =>
          have inward := head
          rw [shape, headRows_first_pair graph m source next rest (shape ▸ path.simple)] at inward
          have adjacent := path.adjacent
          rw [shape] at adjacent
          have outward : graph.expandedMutilatedEdge m (.observed source) next = true := by
            rcases adjacent.1 with arrow | backward
            · exact arrow
            · rw [inward] at backward; cases backward
          cases next with
          | latentPair _ _ => exact False.elim (Bool.false_ne_true outward)
          | observed child =>
              refine ⟨child, ?_⟩
              intro row
              apply Bool.eq_iff_iff.mpr
              rw [decide_eq_true_eq]
              constructor
              · intro read
                have step := (Bool.and_eq_true_iff.mp read).1
                rw [stepOnPath_symm] at step
                exact SeparationNode.observed.inj
                  ((stepOnPath_first_pair (.observed source) (.observed child) (.observed row) rest (shape ▸ path.simple)).mp step)
              · intro same
                subst row
                apply Bool.and_eq_true_iff.mpr
                refine ⟨?_, outward⟩
                rw [stepOnPath_symm]
                exact (stepOnPath_first_pair (.observed source) (.observed child) (.observed child) rest (shape ▸ path.simple)).mpr rfl

/-- An omitted target endpoint has the same unique outgoing-input
classification on the original list.  Reversal changes list order only;
the receiver and kept expanded arrow remain original graph data. -/
theorem target_nonhead_unique_input (path : ActivePath graph m given (.observed source) (.observed target))
    (distinct : source ≠ target) (head : headRows graph m path.nodes target = false) :
    Exists fun child : Fin S.count => forall row,
      incomingEdge graph m path.nodes (.observed target) row = decide (row = child) := by
  have reversedHead : headRows graph m path.reverse.nodes target = false := by
    change headRows graph m path.nodes.reverse target = false
    simpa only [headRows, incomingEdge, stepOnPath_reverse, List.any_reverse] using head
  rcases source_nonhead_unique_input path.reverse (Ne.symm distinct) reversedHead with ⟨child, column⟩
  refine ⟨child, ?_⟩
  intro row
  have reversed := column row
  change incomingEdge graph m path.nodes.reverse (.observed target) row = decide (row = child) at reversed
  simpa only [incomingEdge, stepOnPath_reverse] using reversed

end ActivePathInput

end Causality
end Thesis
