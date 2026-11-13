import Thesis.CausalTransport.ActivePathInputSelection
import Thesis.Probability.FiniteBooleanBasis

namespace Thesis
namespace Causality

universe u

open PathSpecification

/-!
# Identify the observed boundary of the actual path-head interaction

The installed path phase has already been reduced to a computable observed
boundary: selected own rows, XOR the actual outgoing path-parent reads.
Here list simplicity identifies the only neighbours of each occurrence.
Actual DAG adjacency then accounts for every incoming and outgoing arrow.

At an internal noncollider the own and outgoing contributions cancel; an
observed fork has no selected own row and two cancelling outgoing reads.
An internal collider retains one own contribution.  Each distinct observed
endpoint contributes once, irrespective of its incident arrow's direction.
No local neighbour, balance, or collider-readiness premise is added to a
certified path.  Finite decisions only compare graph vertices and Booleans.
-/

variable {S : ObservedSignature.{u}}

namespace ActivePathInput

private instance : DecidableEq (SeparationNode S) := fun left right =>
  if same : SeparationNode.beq left right = true then isTrue ((SeparationNode.beq_eq_true_iff left right).mp same)
  else isFalse (fun equal => same ((SeparationNode.beq_eq_true_iff left right).mpr equal))

/-! ## A simple list fixes the occurrence and its immediate neighbours -/

private theorem split_unique_without_prefix_occurrence {α : Type _}
    (node : α) (before otherBefore after otherAfter : List α)
    (absent : node ∉ before) (otherAbsent : node ∉ otherBefore)
    (same : before ++ node :: after = otherBefore ++ node :: otherAfter) :
    before = otherBefore ∧ after = otherAfter := by
  induction before generalizing otherBefore with
  | nil =>
      cases otherBefore with
      | nil => exact ⟨rfl, (List.cons.inj same).2⟩
      | cons head tail =>
          have equal := (List.cons.inj same).1
          exact False.elim (otherAbsent (List.mem_cons.mpr (Or.inl equal)))
  | cons head tail inductionHypothesis =>
      cases otherBefore with
      | nil =>
          have equal := (List.cons.inj same).1
          exact False.elim (absent (List.mem_cons.mpr (Or.inl equal.symm)))
      | cons otherHead otherTail =>
          have parts := List.cons.inj same
          have rest := inductionHypothesis otherTail
            (fun member => absent (List.mem_cons_of_mem head member))
            (fun member => otherAbsent (List.mem_cons_of_mem otherHead member)) parts.2
          exact ⟨congrArg (fun pair : α × List α => pair.1 :: pair.2)
            (show (head, tail) = (otherHead, otherTail) from Prod.ext parts.1 rest.1), rest.2⟩

private theorem split_unique_of_nodup {α : Type _} {nodes : List α} (simple : nodes.Nodup)
    (node : α) (before otherBefore after otherAfter : List α)
    (first : nodes = before ++ node :: after) (second : nodes = otherBefore ++ node :: otherAfter) :
    before = otherBefore ∧ after = otherAfter := by
  have absent : node ∉ before := by
    intro member
    have parts := List.nodup_append.mp (first ▸ simple)
    exact parts.2.2 node member node List.mem_cons_self rfl
  have otherAbsent : node ∉ otherBefore := by
    intro member
    have parts := List.nodup_append.mp (second ▸ simple)
    exact parts.2.2 node member node List.mem_cons_self rfl
  exact split_unique_without_prefix_occurrence node before otherBefore after otherAfter absent otherAbsent
    (first.symm.trans second)

/-- An actual internal window exhausts the neighbours of its middle
vertex in a simple list.  This is a theorem of the stored list, not a
restriction on which additional edges may exist in the ambient graph. -/
theorem stepOnPath_internal_window {nodes : List (SeparationNode S)} (simple : nodes.Nodup)
    (before after : List (SeparationNode S)) (previous middle next other : SeparationNode S)
    (window : nodes = before ++ previous :: middle :: next :: after) :
    stepOnPath other middle nodes = true ↔ other = previous ∨ other = next := by
  constructor
  · intro selected
    rcases (stepOnPath_eq_true_iff other middle nodes).mp selected with ⟨foundBefore, suffix, forward | backward⟩
    · have first : nodes = (before ++ [previous]) ++ middle :: next :: after := by
        simpa only [List.append_assoc, List.singleton_append] using window
      have second : nodes = (foundBefore ++ [other]) ++ middle :: suffix := by
        simpa only [List.append_assoc, List.singleton_append] using forward
      have positions := split_unique_of_nodup simple middle _ _ _ _ first second
      have ends := congrArg List.getLast? positions.1
      rw [List.getLast?_concat, List.getLast?_concat] at ends
      exact Or.inl (Option.some.inj ends).symm
    · have first : nodes = (before ++ [previous]) ++ middle :: next :: after := by
        simpa only [List.append_assoc, List.singleton_append] using window
      have positions := split_unique_of_nodup simple middle _ _ _ _ first backward
      exact Or.inr (List.cons.inj positions.2).1.symm
  · intro neighbor
    apply (stepOnPath_eq_true_iff other middle nodes).mpr
    rcases neighbor with previousEq | nextEq
    · subst other
      exact ⟨before, next :: after, Or.inl window⟩
    · subst other
      exact ⟨before ++ [previous], after, Or.inr (by
        simpa only [List.append_assoc, List.singleton_append] using window)⟩

/-- The consecutive-pair test forgets only list orientation, not the
arrow orientation subsequently retained by `incomingEdge`. -/
theorem stepOnPath_symm (left right : SeparationNode S) (nodes : List (SeparationNode S)) :
    stepOnPath left right nodes = stepOnPath right left nodes := by
  apply Bool.eq_iff_iff.mpr
  rw [stepOnPath_eq_true_iff, stepOnPath_eq_true_iff]
  constructor
  · rintro ⟨before, after, forward | backward⟩
    · exact ⟨before, after, Or.inr forward⟩
    · exact ⟨before, after, Or.inl backward⟩
  · rintro ⟨before, after, forward | backward⟩
    · exact ⟨before, after, Or.inr forward⟩
    · exact ⟨before, after, Or.inl backward⟩

private theorem internal_neighbors_distinct {nodes : List (SeparationNode S)} (simple : nodes.Nodup)
    (before after : List (SeparationNode S)) (previous middle next : SeparationNode S)
    (window : nodes = before ++ previous :: middle :: next :: after) : previous ≠ next := by
  have tailSimple := (List.nodup_append.mp (window ▸ simple)).2.1
  have unique := (List.nodup_cons.mp tailSimple).1
  intro same
  exact unique (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl same)))

/-- Exactly the incoming arrows from the two actual neighbours select an
internal observed row.  Additional ambient-graph parents remain irrelevant. -/
theorem headRows_internal_window {graph : ObservedGraph S} {m : GraphMutilation S}
    {nodes : List (SeparationNode S)} (simple : nodes.Nodup)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (coordinate : Fin S.count)
    (window : nodes = before ++ previous :: .observed coordinate :: next :: after) :
    headRows graph m nodes coordinate =
      (graph.expandedMutilatedEdge m previous (.observed coordinate) ||
        graph.expandedMutilatedEdge m next (.observed coordinate)) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true_iff]
  constructor
  · intro selected
    rcases List.any_eq_true.mp selected with ⟨parent, _member, incoming⟩
    have parts := Bool.and_eq_true_iff.mp incoming
    rcases (stepOnPath_internal_window simple before after previous _ next parent window).mp parts.1 with left | right
    · exact Or.inl (by simpa only [left] using parts.2)
    · exact Or.inr (by simpa only [right] using parts.2)
  · intro incoming
    rcases incoming with left | right
    · apply incomingEdge_head
      exact Bool.and_eq_true_iff.mpr ⟨(stepOnPath_internal_window simple before after previous _ next previous window).mpr
        (Or.inl rfl), left⟩
    · apply incomingEdge_head
      exact Bool.and_eq_true_iff.mpr ⟨(stepOnPath_internal_window simple before after previous _ next next window).mpr
        (Or.inr rfl), right⟩

private theorem xor_fold_split {α : Type _} (left right : α -> Bool) (nodes : List α) (first second : Bool) :
    nodes.foldl (fun total node => Bool.xor total (Bool.xor (left node) (right node))) (Bool.xor first second) =
      Bool.xor (nodes.foldl (fun total node => Bool.xor total (left node)) first)
        (nodes.foldl (fun total node => Bool.xor total (right node)) second) := by
  induction nodes generalizing first second with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.foldl_cons]
      have accumulators : Bool.xor (Bool.xor first second) (Bool.xor (left head) (right head)) =
          Bool.xor (Bool.xor first (left head)) (Bool.xor second (right head)) := by
        cases first <;> cases second <;> cases left head <;> cases right head <;> rfl
      rw [accumulators]
      exact inductionHypothesis _ _

private theorem xor_fold_zero {α : Type _} (nodes : List α) (seed : Bool) :
    nodes.foldl (fun total _ => Bool.xor total false) seed = seed := by
  induction nodes generalizing seed with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, Bool.xor_false]
      exact inductionHypothesis seed

private def outgoingNeighbor (graph : ObservedGraph S) (m : GraphMutilation S)
    (coordinate : Fin S.count) (neighbor : SeparationNode S) (child : Fin S.count) : Bool :=
  if .observed child = neighbor then graph.expandedMutilatedEdge m (.observed coordinate) neighbor else false

private theorem outgoingNeighbor_fold (graph : ObservedGraph S) (m : GraphMutilation S)
    (coordinate : Fin S.count) (neighbor : SeparationNode S) :
    (List.finRange S.count).foldl (fun total child => Bool.xor total (outgoingNeighbor graph m coordinate neighbor child)) false =
      graph.expandedMutilatedEdge m (.observed coordinate) neighbor := by
  cases neighbor with
  | latentPair left right =>
      have inputs : (fun child => outgoingNeighbor graph m coordinate (.latentPair left right) child) = (fun _ => false) := by
        funext child
        unfold outgoingNeighbor
        split
        · rename_i impossible; cases impossible
        · rfl
      exact (congrArg (fun bits : Fin S.count -> Bool =>
        (List.finRange S.count).foldl (fun total child => Bool.xor total (bits child)) false) inputs).trans
          (xor_fold_zero _ false)
  | observed child =>
      let bit := graph.expandedMutilatedEdge m (.observed coordinate) (.observed child)
      have inputs : (fun node => outgoingNeighbor graph m coordinate (.observed child) node) =
          (fun node => if bit then Probability.FiniteBooleanInteraction.basisAssignment S.count child node else false) := by
        funext node
        by_cases same : node = child
        · subst node
          rw [Probability.FiniteBooleanInteraction.basisAssignment_self]
          unfold outgoingNeighbor
          rw [if_pos rfl]
          change bit = if bit then true else false
          cases bit <;> rfl
        · have different : (SeparationNode.observed node : SeparationNode S) ≠ .observed child :=
            fun equal => same (SeparationNode.observed.inj equal)
          rw [Probability.FiniteBooleanInteraction.basisAssignment_eq_false_of_ne S.count child node same]
          unfold outgoingNeighbor
          rw [if_neg different]
          exact (ite_self false).symm
      exact (congrArg (fun bits : Fin S.count -> Bool =>
        (List.finRange S.count).foldl (fun total node => Bool.xor total (bits node)) false) inputs).trans
          (Probability.FiniteBooleanInteraction.basisAssignment_masked_foldl S.count child (fun _ => bit))

private theorem outgoing_internal_window {graph : ObservedGraph S} {m : GraphMutilation S}
    {nodes : List (SeparationNode S)} (simple : nodes.Nodup)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (coordinate child : Fin S.count)
    (window : nodes = before ++ previous :: .observed coordinate :: next :: after) :
    incomingEdge graph m nodes (.observed coordinate) child = Bool.xor
      (outgoingNeighbor graph m coordinate previous child) (outgoingNeighbor graph m coordinate next child) := by
  have different := internal_neighbors_distinct simple before after previous (.observed coordinate) next window
  by_cases atPrevious : (SeparationNode.observed child : SeparationNode S) = previous
  · have notNext : (SeparationNode.observed child : SeparationNode S) ≠ next :=
      fun same => different (atPrevious.symm.trans same)
    have step := (stepOnPath_internal_window simple before after previous (.observed coordinate) next (.observed child) window).mpr
      (Or.inl atPrevious)
    unfold incomingEdge outgoingNeighbor
    rw [stepOnPath_symm, step, Bool.true_and, if_pos atPrevious, if_neg notNext, Bool.xor_false, atPrevious]
  · by_cases atNext : (SeparationNode.observed child : SeparationNode S) = next
    · have step := (stepOnPath_internal_window simple before after previous (.observed coordinate) next (.observed child) window).mpr
        (Or.inr atNext)
      unfold incomingEdge outgoingNeighbor
      rw [stepOnPath_symm, step, Bool.true_and, if_neg atPrevious, if_pos atNext, Bool.false_xor, atNext]
    · have absent : stepOnPath (.observed child) (.observed coordinate) nodes = false := by
        cases selected : stepOnPath (.observed child) (.observed coordinate) nodes with
        | false => rfl
        | true =>
            rcases (stepOnPath_internal_window simple before after previous (.observed coordinate) next (.observed child) window).mp
              selected with left | right
            · exact False.elim (atPrevious left)
            · exact False.elim (atNext right)
      unfold incomingEdge outgoingNeighbor
      rw [stepOnPath_symm, absent, Bool.false_and, if_neg atPrevious, if_neg atNext]
      rfl

/-- The outgoing fold includes exactly the two actual internal neighbours.
A latent neighbour contributes zero because no observed-to-latent arrow
exists; actual observed neighbours contribute their kept arrow once each. -/
theorem outgoingFold_internal_window {graph : ObservedGraph S} {m : GraphMutilation S}
    {nodes : List (SeparationNode S)} (simple : nodes.Nodup)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (coordinate : Fin S.count)
    (window : nodes = before ++ previous :: .observed coordinate :: next :: after) :
    (List.finRange S.count).foldl (fun total child => Bool.xor total (incomingEdge graph m nodes (.observed coordinate) child)) false =
      Bool.xor (graph.expandedMutilatedEdge m (.observed coordinate) previous)
        (graph.expandedMutilatedEdge m (.observed coordinate) next) := by
  have inputs := funext (fun child => outgoing_internal_window (graph := graph) (m := m)
    simple before after previous next coordinate child window)
  have actualFold := congrArg (fun bits : Fin S.count -> Bool =>
    (List.finRange S.count).foldl (fun total child => Bool.xor total (bits child)) false) inputs
  exact actualFold.trans ((xor_fold_split _ _ _ false false).trans (by
    rw [outgoingNeighbor_fold, outgoingNeighbor_fold]))

private theorem adjacent_reverse_edge (graph : ObservedGraph S) (m : GraphMutilation S)
    (left right : SeparationNode S) (adjacent : Adjacent graph m left right) :
    graph.expandedMutilatedEdge m right left = !(graph.expandedMutilatedEdge m left right) := by
  cases forward : graph.expandedMutilatedEdge m left right with
  | false =>
      rcases adjacent with impossible | backward
      · rw [forward] at impossible; cases impossible
      · rw [backward]; rfl
  | true =>
      cases backward : graph.expandedMutilatedEdge m right left with
      | false => rfl
      | true => exact False.elim (Nat.lt_asymm (graph.expandedMutilatedEdge_rank_lt m forward)
          (graph.expandedMutilatedEdge_rank_lt m backward))

/-- Every internal observed coordinate contributes precisely its actual
collider bit to the head-phase boundary.  Chains cancel own/outgoing reads;
forks cancel their two outgoing reads without adding an own row.  The DAG
rank excludes opposite arrows, so each adjacent edge has one orientation. -/
theorem observedBoundary_internal_window {graph : ObservedGraph S} {m : GraphMutilation S}
    {nodes : List (SeparationNode S)} (simple : nodes.Nodup)
    (consecutive : Consecutive (Adjacent graph m) nodes)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (coordinate : Fin S.count)
    (window : nodes = before ++ previous :: .observed coordinate :: next :: after) :
    observedBoundary graph m nodes coordinate = isColliderBool graph m previous (.observed coordinate) next := by
  have first := Consecutive.pair_of_append before (next :: after) previous (.observed coordinate) (window ▸ consecutive)
  have second := Consecutive.pair_of_append (relation := Adjacent graph m) (before ++ [previous]) after
    (.observed coordinate) next (by simpa only [List.append_assoc, List.singleton_append] using window ▸ consecutive)
  unfold observedBoundary isColliderBool
  rw [headRows_internal_window simple before after previous next coordinate window,
    outgoingFold_internal_window simple before after previous next coordinate window,
    adjacent_reverse_edge graph m previous (.observed coordinate) first,
    adjacent_reverse_edge graph m next (.observed coordinate) second.symm]
  cases graph.expandedMutilatedEdge m previous (.observed coordinate) <;>
    cases graph.expandedMutilatedEdge m next (.observed coordinate) <;> rfl

/-! ## Distinct observed endpoints each contribute one boundary bit -/

/-- At the first occurrence of a simple non-singleton list, the only
consecutive neighbour is the displayed second vertex.  This endpoint fact
also supports actual local-input evaluation; it assumes no edge direction. -/
theorem stepOnPath_first_pair (first next other : SeparationNode S) (rest : List (SeparationNode S))
    (simple : (first :: next :: rest).Nodup) :
    stepOnPath other first (first :: next :: rest) = true ↔ other = next := by
  constructor
  · intro selected
    rcases (stepOnPath_eq_true_iff other first _).mp selected with ⟨before, after, forward | backward⟩
    · have second : first :: next :: rest = (before ++ [other]) ++ first :: after := by
        simpa only [List.append_assoc, List.singleton_append] using forward
      have positions := split_unique_of_nodup simple first [] (before ++ [other]) (next :: rest) after rfl second
      have lengths := congrArg List.length positions.1
      simp only [List.length_nil, List.length_append, List.length_singleton] at lengths
      omega
    · have positions := split_unique_of_nodup simple first [] before (next :: rest) (other :: after) rfl backward
      exact (List.cons.inj positions.2).1.symm
  · intro same
    subst other
    exact (stepOnPath_eq_true_iff next first _).mpr ⟨[], rest, Or.inr rfl⟩

/-- A first observed endpoint is selected exactly when its one actual
neighbour has a kept incoming arrow.  An outgoing endpoint is not a head. -/
theorem headRows_first_pair (graph : ObservedGraph S) (m : GraphMutilation S) (coordinate : Fin S.count)
    (next : SeparationNode S) (rest : List (SeparationNode S)) (simple : (.observed coordinate :: next :: rest).Nodup) :
    headRows graph m (.observed coordinate :: next :: rest) coordinate =
      graph.expandedMutilatedEdge m next (.observed coordinate) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro selected
    rcases List.any_eq_true.mp selected with ⟨parent, _member, incoming⟩
    have parts := Bool.and_eq_true_iff.mp incoming
    have same := (stepOnPath_first_pair (.observed coordinate) next parent rest simple).mp parts.1
    simpa only [same] using parts.2
  · intro incoming
    apply incomingEdge_head
    exact Bool.and_eq_true_iff.mpr ⟨(stepOnPath_first_pair (.observed coordinate) next next rest simple).mpr rfl, incoming⟩

private theorem outgoing_first_pair (graph : ObservedGraph S) (m : GraphMutilation S) (coordinate child : Fin S.count)
    (next : SeparationNode S) (rest : List (SeparationNode S)) (simple : (.observed coordinate :: next :: rest).Nodup) :
    incomingEdge graph m (.observed coordinate :: next :: rest) (.observed coordinate) child =
      outgoingNeighbor graph m coordinate next child := by
  by_cases same : (SeparationNode.observed child : SeparationNode S) = next
  · have step := (stepOnPath_first_pair (.observed coordinate) next (.observed child) rest simple).mpr same
    unfold incomingEdge outgoingNeighbor
    rw [stepOnPath_symm, step, Bool.true_and, if_pos same, same]
  · have absent : stepOnPath (.observed child) (.observed coordinate) (.observed coordinate :: next :: rest) = false := by
      cases selected : stepOnPath (.observed child) (.observed coordinate) (.observed coordinate :: next :: rest) with
      | false => rfl
      | true => exact False.elim (same ((stepOnPath_first_pair (.observed coordinate) next (.observed child) rest simple).mp selected))
    unfold incomingEdge outgoingNeighbor
    rw [stepOnPath_symm, absent, Bool.false_and, if_neg same]

private theorem observedBoundary_first_pair (graph : ObservedGraph S) (m : GraphMutilation S) (coordinate : Fin S.count)
    (next : SeparationNode S) (rest : List (SeparationNode S)) (simple : (.observed coordinate :: next :: rest).Nodup)
    (adjacent : Adjacent graph m (.observed coordinate) next) :
    observedBoundary graph m (.observed coordinate :: next :: rest) coordinate = true := by
  have inputs := funext (fun child => outgoing_first_pair graph m coordinate child next rest simple)
  have outgoing := (congrArg (fun bits : Fin S.count -> Bool =>
    (List.finRange S.count).foldl (fun total child => Bool.xor total (bits child)) false) inputs).trans
      (outgoingNeighbor_fold graph m coordinate next)
  unfold observedBoundary
  rw [headRows_first_pair graph m coordinate next rest simple, outgoing,
    adjacent_reverse_edge graph m (.observed coordinate) next adjacent]
  cases graph.expandedMutilatedEdge m (.observed coordinate) next <;> rfl

/-- The source endpoint contributes once, with no requirement that its
incident edge already be incoming.  Distinct endpoints exclude a singleton
path, and actual simplicity excludes any second occurrence of the source. -/
theorem observedBoundary_source {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
    {source target : Fin S.count} (path : ActivePath graph m given (.observed source) (.observed target))
    (distinct : source ≠ target) : observedBoundary graph m path.nodes source = true := by
  cases shape : path.nodes with
  | nil => have impossible := path.starts; rw [shape] at impossible; cases impossible
  | cons head tail =>
      have starts := path.starts
      rw [shape] at starts
      have same := Option.some.inj starts
      subst head
      cases tail with
      | nil =>
          have finishes := path.finishes
          rw [shape] at finishes
          exact False.elim (distinct (SeparationNode.observed.inj (Option.some.inj finishes)))
      | cons next rest =>
          exact shape ▸ observedBoundary_first_pair graph m source next rest (shape ▸ path.simple)
            (by have adjacent := path.adjacent; rw [shape] at adjacent; exact adjacent.1)

private theorem stepOnPath_reverse_of_true {left right : SeparationNode S} {nodes : List (SeparationNode S)}
    (selected : stepOnPath left right nodes = true) : stepOnPath left right nodes.reverse = true := by
  rcases (stepOnPath_eq_true_iff left right nodes).mp selected with ⟨before, after, forward | backward⟩
  · apply (stepOnPath_eq_true_iff left right _).mpr
    refine ⟨after.reverse, before.reverse, Or.inr ?_⟩
    rw [forward]
    simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
  · apply (stepOnPath_eq_true_iff left right _).mpr
    refine ⟨after.reverse, before.reverse, Or.inl ?_⟩
    rw [backward]
    simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- Reversing the list preserves the exact consecutive-pair scan. -/
theorem stepOnPath_reverse (left right : SeparationNode S) (nodes : List (SeparationNode S)) :
    stepOnPath left right nodes.reverse = stepOnPath left right nodes := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro selected
    simpa only [List.reverse_reverse] using stepOnPath_reverse_of_true selected
  · exact stepOnPath_reverse_of_true

/-- The boundary is independent of list traversal direction.  The graph
and its kept-arrow directions are unchanged; only the pair scan is reversed. -/
theorem observedBoundary_reverse (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (coordinate : Fin S.count) :
    observedBoundary graph m nodes.reverse coordinate = observedBoundary graph m nodes coordinate := by
  simp only [observedBoundary, headRows, incomingEdge, stepOnPath_reverse, List.any_reverse]

/-- The observed target contributes once by the same source-endpoint
argument on the certified reversed path, without inventing a final window. -/
theorem observedBoundary_target {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
    {source target : Fin S.count} (path : ActivePath graph m given (.observed source) (.observed target))
    (distinct : source ≠ target) : observedBoundary graph m path.nodes target = true := by
  have reversed := observedBoundary_source path.reverse (Ne.symm distinct)
  change observedBoundary graph m path.nodes.reverse target = true at reversed
  rw [observedBoundary_reverse] at reversed
  exact reversed

/-! ## The same actual collider scan serves phase balance and activation selection -/

private def colliderAt (graph : ObservedGraph S) (m : GraphMutilation S)
    (collider : Fin S.count) : List (SeparationNode S) -> Bool
  | previous :: middle :: next :: rest =>
      (SeparationNode.beq middle (.observed collider) && isColliderBool graph m previous middle next) ||
        colliderAt graph m collider (middle :: next :: rest)
  | _ => false

private theorem colliderAt_eq_true_iff (graph : ObservedGraph S) (m : GraphMutilation S)
    (collider : Fin S.count) (nodes : List (SeparationNode S)) :
    colliderAt graph m collider nodes = true ↔
      Exists fun before : List (SeparationNode S) => Exists fun after : List (SeparationNode S) =>
        Exists fun previous : SeparationNode S => Exists fun next : SeparationNode S =>
          nodes = before ++ previous :: .observed collider :: next :: after ∧
            IsCollider graph m previous (.observed collider) next := by
  induction nodes with
  | nil =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨before, after, previous, next, window, _⟩
        have lengths := congrArg List.length window
        simp only [List.length_nil, List.length_append, List.length_cons] at lengths
        omega
  | cons previous tail inductionHypothesis =>
      cases tail with
      | nil =>
          constructor
          · intro impossible; cases impossible
          · rintro ⟨before, after, first, next, window, _⟩
            have lengths := congrArg List.length window
            simp only [List.length_nil, List.length_append, List.length_cons] at lengths
            omega
      | cons middle rest =>
          cases rest with
          | nil =>
              constructor
              · intro impossible; cases impossible
              · rintro ⟨before, after, first, next, window, _⟩
                have lengths := congrArg List.length window
                simp only [List.length_nil, List.length_append, List.length_cons] at lengths
                omega
          | cons next rest =>
              rw [colliderAt, Bool.or_eq_true_iff, Bool.and_eq_true_iff]
              constructor
              · intro found
                rcases found with here | later
                · have same := (SeparationNode.beq_eq_true_iff middle (.observed collider)).mp here.1
                  subst middle
                  exact ⟨[], rest, previous, next, rfl,
                    (IsCollider_iff_isColliderBool graph m previous (.observed collider) next).mpr here.2⟩
                · rcases inductionHypothesis.mp later with ⟨before, after, first, last, window, actual⟩
                  exact ⟨previous :: before, after, first, last, congrArg (List.cons previous) window, actual⟩
              · rintro ⟨before, after, first, last, window, actual⟩
                cases before with
                | nil =>
                    have heads := List.cons.inj window
                    have middles := List.cons.inj heads.2
                    have lasts := List.cons.inj middles.2
                    have firstEq := heads.1
                    have middleEq := middles.1
                    have lastEq := lasts.1
                    subst first
                    subst middle
                    subst last
                    exact Or.inl ⟨(SeparationNode.beq_eq_true_iff _ _).mpr rfl,
                      (IsCollider_iff_isColliderBool graph m _ _ _).mp actual⟩
                | cons head before =>
                    have tails := (List.cons.inj window).2
                    exact Or.inr (inductionHypothesis.mpr ⟨before, after, first, last, tails, actual⟩)

/-- Select exactly the observed internal collider rows of the stored path.
Endpoints are never scanned as windows; every selected row has both actual
incoming path arrows, not merely an activated ancestor elsewhere. -/
def colliderRows (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) : NodeSet S := fun child => colliderAt graph m child nodes

/-- The executable row mask has exactly the displayed actual collider
windows.  The decomposition is used in proofs, not selected as data. -/
theorem colliderRows_eq_true_iff (graph : ObservedGraph S) (m : GraphMutilation S)
    (child : Fin S.count) (nodes : List (SeparationNode S)) :
    colliderRows graph m nodes child = true ↔
      Exists fun before : List (SeparationNode S) => Exists fun after : List (SeparationNode S) =>
        Exists fun previous : SeparationNode S => Exists fun next : SeparationNode S =>
          nodes = before ++ previous :: .observed child :: next :: after ∧
            IsCollider graph m previous (.observed child) next :=
  colliderAt_eq_true_iff graph m child nodes

/-- Two internal windows at the same occurrence have identical immediate
neighbours.  Simplicity makes their middle-position decompositions unique. -/
theorem internal_window_neighbors_unique {nodes : List (SeparationNode S)} (simple : nodes.Nodup)
    (before after otherBefore otherAfter : List (SeparationNode S))
    (previous middle next otherPrevious otherNext : SeparationNode S)
    (first : nodes = before ++ previous :: middle :: next :: after)
    (second : nodes = otherBefore ++ otherPrevious :: middle :: otherNext :: otherAfter) :
    previous = otherPrevious ∧ next = otherNext := by
  have firstSplit : nodes = (before ++ [previous]) ++ middle :: next :: after := by
    simpa only [List.append_assoc, List.singleton_append] using first
  have secondSplit : nodes = (otherBefore ++ [otherPrevious]) ++ middle :: otherNext :: otherAfter := by
    simpa only [List.append_assoc, List.singleton_append] using second
  have positions := split_unique_of_nodup simple middle _ _ _ _ firstSplit secondSplit
  have ends := congrArg List.getLast? positions.1
  rw [List.getLast?_concat, List.getLast?_concat] at ends
  exact ⟨Option.some.inj ends, (List.cons.inj positions.2).1⟩

/-- The collider scan agrees with the actual internal window at each
simple observed occurrence.  It cannot select another window elsewhere. -/
theorem colliderRows_internal_window {graph : ObservedGraph S} {m : GraphMutilation S}
    {nodes : List (SeparationNode S)} (simple : nodes.Nodup)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (coordinate : Fin S.count)
    (window : nodes = before ++ previous :: .observed coordinate :: next :: after) :
    colliderRows graph m nodes coordinate = isColliderBool graph m previous (.observed coordinate) next := by
  apply Bool.eq_iff_iff.mpr
  rw [colliderRows_eq_true_iff, ← IsCollider_iff_isColliderBool graph m previous (.observed coordinate) next]
  constructor
  · rintro ⟨otherBefore, otherAfter, otherPrevious, otherNext, otherWindow, collider⟩
    have neighbors := internal_window_neighbors_unique simple before after otherBefore otherAfter previous _ next
      otherPrevious otherNext window otherWindow
    simpa only [← neighbors.1, ← neighbors.2] using collider
  · intro collider
    exact ⟨before, after, previous, next, window, collider⟩

private theorem colliderRows_false_of_not_mem {graph : ObservedGraph S} {m : GraphMutilation S}
    {nodes : List (SeparationNode S)} {coordinate : Fin S.count} (absent : .observed coordinate ∉ nodes) :
    colliderRows graph m nodes coordinate = false := by
  cases selected : colliderRows graph m nodes coordinate with
  | false => rfl
  | true =>
      rcases (colliderRows_eq_true_iff graph m coordinate nodes).mp selected with ⟨before, after, previous, next, window, _⟩
      exact False.elim (absent (window ▸ List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- A source endpoint is never an internal collider row, including for a
singleton path.  This is derived from starts and simplicity, not activity. -/
theorem colliderRows_source_false {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
    {source target : Fin S.count} (path : ActivePath graph m given (.observed source) (.observed target)) :
    colliderRows graph m path.nodes source = false := by
  cases selected : colliderRows graph m path.nodes source with
  | false => rfl
  | true =>
      rcases (colliderRows_eq_true_iff graph m source path.nodes).mp selected with ⟨before, after, previous, next, window, _⟩
      cases shape : path.nodes with
      | nil => have impossible := path.starts; rw [shape] at impossible; cases impossible
      | cons head tail =>
          have starts := path.starts
          rw [shape] at starts
          have same := Option.some.inj starts
          subst head
          have second : path.nodes = (before ++ [previous]) ++ .observed source :: next :: after := by
            simpa only [List.append_assoc, List.singleton_append] using window
          have positions := split_unique_of_nodup path.simple (.observed source) [] (before ++ [previous]) tail (next :: after)
            shape second
          have lengths := congrArg List.length positions.1
          simp only [List.length_nil, List.length_append, List.length_singleton] at lengths
          omega

/-- The target endpoint is likewise never an internal collider row.  The
actual last-element decomposition makes its empty suffix explicit. -/
theorem colliderRows_target_false {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
    {source target : Fin S.count} (path : ActivePath graph m given (.observed source) (.observed target)) :
    colliderRows graph m path.nodes target = false := by
  cases selected : colliderRows graph m path.nodes target with
  | false => rfl
  | true =>
      rcases (colliderRows_eq_true_iff graph m target path.nodes).mp selected with ⟨before, after, previous, next, window, _⟩
      rcases List.getLast?_eq_some_iff.mp path.finishes with ⟨lastBefore, lastWindow⟩
      have first : path.nodes = (before ++ [previous]) ++ .observed target :: next :: after := by
        simpa only [List.append_assoc, List.singleton_append] using window
      have positions := split_unique_of_nodup path.simple (.observed target) (before ++ [previous]) lastBefore (next :: after) []
        first lastWindow
      cases positions.2

private theorem observedBoundary_false_of_not_mem {graph : ObservedGraph S} {m : GraphMutilation S}
    {nodes : List (SeparationNode S)} {coordinate : Fin S.count} (absent : .observed coordinate ∉ nodes) :
    observedBoundary graph m nodes coordinate = false := by
  have noHead : headRows graph m nodes coordinate = false := by
    cases selected : headRows graph m nodes coordinate with
    | false => rfl
    | true => exact False.elim (absent (headRows_member selected))
  have inputs : (fun child => incomingEdge graph m nodes (.observed coordinate) child) = (fun _ => false) := by
    funext child
    cases selected : incomingEdge graph m nodes (.observed coordinate) child with
    | false => rfl
    | true => exact False.elim (absent (stepOnPath_members (Bool.and_eq_true_iff.mp selected).1).1)
  have outgoing := (congrArg (fun bits : Fin S.count -> Bool =>
    (List.finRange S.count).foldl (fun total child => Bool.xor total (bits child)) false) inputs).trans (xor_fold_zero _ false)
  unfold observedBoundary
  rw [noHead, outgoing]
  rfl

/-- The explicit endpoint/collider character, with Boolean XOR preserving
the intended parity.  Actual path endpoints are proved absent from the
internal collider mask above; no disjointness premise is supplied here. -/
def endpointColliderBoundary (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (source target : Fin S.count) : NodeSet S :=
  fun coordinate => Bool.xor (decide (coordinate = source))
    (Bool.xor (decide (coordinate = target)) (colliderRows graph m nodes coordinate))

/-- The complete observed boundary of any simple active path with distinct
observed endpoints is exactly the two endpoint bits XOR all actual internal
collider bits.  This supplies the graph identity, not a requested matching
character premise.  No first-edge orientation or collider-free restriction
is needed; the incoming source constraint belongs only to the later odd
direction argument. -/
theorem observedBoundary_eq_endpointColliderBoundary {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
    {source target : Fin S.count} (path : ActivePath graph m given (.observed source) (.observed target))
    (distinct : source ≠ target) :
    observedBoundary graph m path.nodes = endpointColliderBoundary graph m path.nodes source target := by
  funext coordinate
  by_cases atSource : coordinate = source
  · subst coordinate
    rw [observedBoundary_source path distinct]
    unfold endpointColliderBoundary
    rw [decide_eq_true rfl, decide_eq_false distinct, colliderRows_source_false path]
    rfl
  · by_cases atTarget : coordinate = target
    · subst coordinate
      rw [observedBoundary_target path distinct]
      unfold endpointColliderBoundary
      rw [decide_eq_false (Ne.symm distinct), decide_eq_true rfl, colliderRows_target_false path]
      rfl
    · unfold endpointColliderBoundary
      rw [decide_eq_false atSource, decide_eq_false atTarget, Bool.false_xor, Bool.false_xor]
      by_cases member : (SeparationNode.observed coordinate : SeparationNode S) ∈ path.nodes
      · rcases exists_internal_neighbors_of_mem path.starts path.finishes member
          (fun same => atSource (SeparationNode.observed.inj same))
          (fun same => atTarget (SeparationNode.observed.inj same)) with ⟨before, previous, next, after, window⟩
        exact (observedBoundary_internal_window path.simple path.adjacent before after previous next coordinate window).trans
          (colliderRows_internal_window path.simple before after previous next coordinate window).symm
      · rw [observedBoundary_false_of_not_mem member, colliderRows_false_of_not_mem member]

end ActivePathInput
end Causality
end Thesis
