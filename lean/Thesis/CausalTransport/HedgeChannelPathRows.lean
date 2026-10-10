import Thesis.CausalTransport.ActivePathRootInputs
import Thesis.CausalTransport.HedgeChannelPathInputs

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction

/-!
# Evaluate actual path rows from their immediate incoming inputs

Global phase conservation does not establish evenness of each background
row.  This module expands the actual installed parent and reserved-root
folds at an internal observed window.  They read exactly the two displayed
neighbours whose arrows enter that row, each at its original cube coordinate.
Ambient off-path parents and unused roots contribute nothing.

The identities hold at every cube assignment.  They neither assume local
parity nor replace the guarded local interpreter with global cube access.
`expandedInput` is a proof-level way to describe those legal reads; the
installed mechanism remains `LinearSignal.ofActivePath`.

The internal-window identity is a step toward the constructive supported
odd direction, not its replacement.  Endpoint evaluation, support on the
actual conditioning cylinder, and parity of every selected row still need
to be derived for that direction.  Activation installation and integration
of all mandatory Small rows remain separate conditional-completeness work.
-/

variable {S : ObservedSignature.{0}}

namespace HedgeChannelEnvironmentInstallation
namespace LinearSignal

variable {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
  {source target : Fin S.count}

/-- The original coordinate named by an expanded path vertex.  An observed
vertex names its observed bit; a genuine latent pair names its original
reserved root, with either alias selecting the same coordinate.  An inactive
pair returns false, so this total description grants no unavailable input. -/
def expandedInput (graph : ObservedGraph S) (point : Cube graph) : SeparationNode S -> Bool
  | .observed child => cubeSample graph point child
  | .latentPair left right =>
      if edge : graph.bidirected left right = true then
        cubeEnvironment graph point (pairRootBetween graph edge)
      else false

/-- The named coordinate contributes to a row only when its actual kept
arrow enters that row in the supplied mutilated graph. -/
def incomingValue (graph : ObservedGraph S) (m : GraphMutilation S)
    (point : Cube graph) (neighbor : SeparationNode S) (child : Fin S.count) : Bool :=
  graph.expandedMutilatedEdge m neighbor (.observed child) && expandedInput graph point neighbor

private theorem masked_indicator_fold {count : Nat} (coordinate : Fin count) (bits : Fin count -> Bool) :
    (List.finRange count).foldl (fun total index => Bool.xor total
      (decide (index = coordinate) && bits index)) false = bits coordinate := by
  have same : (fun total index => Bool.xor total (decide (index = coordinate) && bits index)) =
      (fun total index => Bool.xor total (if bits index then basisAssignment count coordinate index else false)) := by
    funext total index
    unfold basisAssignment
    cases bits index <;> cases decide (index = coordinate) <;> rfl
  rw [same, basisAssignment_masked_foldl]

private def observedNeighborRead (graph : ObservedGraph S) (m : GraphMutilation S)
    (point : Cube graph) (child : Fin S.count) (neighbor : SeparationNode S) (parent : Fin S.count) : Bool :=
  SeparationNode.beq (.observed parent) neighbor &&
    graph.expandedMutilatedEdge m (.observed parent) (.observed child) && cubeSample graph point parent

private def reservedNeighborRead (graph : ObservedGraph S) (m : GraphMutilation S)
    (point : Cube graph) (child : Fin S.count) (neighbor : SeparationNode S)
    (root : Fin (pairRootCount graph.binary)) : Bool :=
  ActivePathInput.rootAt graph root neighbor &&
    graph.expandedMutilatedEdge m neighbor (.observed child) && cubeEnvironment graph point root

private theorem observedNeighbor_fold (point : Cube graph) (child : Fin S.count) (neighbor : SeparationNode S) :
    (List.finRange S.count).foldl (fun total parent => Bool.xor total
      (observedNeighborRead graph m point child neighbor parent)) false =
      match neighbor with
      | .observed parent => incomingValue graph m point (.observed parent) child
      | .latentPair _ _ => false := by
  cases neighbor with
  | observed coordinate =>
      have same : forall parent, observedNeighborRead graph m point child (.observed coordinate) parent =
          (decide (parent = coordinate) &&
            (graph.expandedMutilatedEdge m (.observed parent) (.observed child) && cubeSample graph point parent)) := by
        intro parent
        have test : SeparationNode.beq (.observed parent) (.observed coordinate) = decide (parent = coordinate) := by
          apply Bool.eq_iff_iff.mpr
          rw [SeparationNode.beq_eq_true_iff, decide_eq_true_eq, SeparationNode.observed.injEq]
        simp only [observedNeighborRead, test, Bool.and_assoc]
      have actualFold := foldl_congr _ _ false (List.finRange S.count)
        (fun total parent => congrArg (Bool.xor total) (same parent))
      exact actualFold.trans (masked_indicator_fold coordinate _)
  | latentPair left right =>
      have absent : forall parent, SeparationNode.beq (.observed parent) (.latentPair left right) = false := by
        intro parent
        apply Bool.eq_false_iff.mpr
        intro impossible
        cases (SeparationNode.beq_eq_true_iff _ _).mp impossible
      simp only [observedNeighborRead, absent, Bool.false_and]
      exact foldl_unchanged _ _ _ (fun total _index => Bool.xor_false total)

private theorem reservedNeighbor_fold
    (path : ActivePath graph m given (.observed source) (.observed target))
    (point : Cube graph) (child : Fin S.count) (neighbor : SeparationNode S) (member : neighbor ∈ path.nodes) :
    (List.finRange (pairRootCount graph.binary)).foldl (fun total root => Bool.xor total
      (reservedNeighborRead graph m point child neighbor root)) false =
      match neighbor with
      | .observed _ => false
      | .latentPair left right => incomingValue graph m point (.latentPair left right) child := by
  cases neighbor with
  | observed coordinate =>
      simp only [reservedNeighborRead, ActivePathInput.rootAt_observed, Bool.false_and]
      exact foldl_unchanged _ _ _ (fun total _index => Bool.xor_false total)
  | latentPair left right =>
      have same : forall root, reservedNeighborRead graph m point child (.latentPair left right) root =
          (decide (root = path.pairRootOfLatent left right member) &&
            (graph.expandedMutilatedEdge m (.latentPair left right) (.observed child) && cubeEnvironment graph point root)) := by
        intro root
        simp only [reservedNeighborRead, ActivePathInput.rootAt_latent_eq_index path left right member root,
          Bool.and_assoc]
        rfl
      have actualFold := foldl_congr _ _ false (List.finRange (pairRootCount graph.binary))
        (fun total root => congrArg (Bool.xor total) (same root))
      rw [actualFold, masked_indicator_fold]
      change (graph.expandedMutilatedEdge m (.latentPair left right) (.observed child) &&
        cubeEnvironment graph point (path.pairRootOfLatent left right member)) =
        (graph.expandedMutilatedEdge m (.latentPair left right) (.observed child) &&
          (if edge : graph.bidirected left right = true then
            cubeEnvironment graph point (pairRootBetween graph edge) else false))
      rw [dif_pos (path.latentPair_is_bidirected left right member)]
      rfl

private theorem neighbor_folds (path : ActivePath graph m given (.observed source) (.observed target))
    (point : Cube graph) (child : Fin S.count) (neighbor : SeparationNode S) (member : neighbor ∈ path.nodes) :
    Bool.xor
      ((List.finRange S.count).foldl (fun total parent => Bool.xor total
        (observedNeighborRead graph m point child neighbor parent)) false)
      ((List.finRange (pairRootCount graph.binary)).foldl (fun total root => Bool.xor total
        (reservedNeighborRead graph m point child neighbor root)) false) =
      incomingValue graph m point neighbor child := by
  rw [observedNeighbor_fold, reservedNeighbor_fold path point child neighbor member]
  cases neighbor <;> simp only [Bool.xor_false, Bool.false_xor]

/-! ## Normalize the actual installed interpreter, retaining both guards -/

private theorem ofActivePath_actual_row
    (path : ActivePath graph m given (.observed source) (.observed target)) (child : Fin S.count) (point : Cube graph) :
    ((ofActivePath path).rowPhase child).value point = Bool.xor (cubeSample graph point child)
      (Bool.xor
        ((List.finRange S.count).foldl (fun total parent => Bool.xor total
          (ActivePathInput.incomingEdge graph m path.nodes (.observed parent) child && cubeSample graph point parent)) false)
        ((List.finRange (pairRootCount graph.binary)).foldl (fun total root => Bool.xor total
          (ActivePathInput.pairUsed graph path.nodes root && pairRootIncident graph.binary root child &&
            cubeEnvironment graph point root)) false)) := by
  rw [rowPhase_value]
  congr 2
  · apply foldl_congr
    intro total parent
    cases selected : (ofActivePath path).parentMask child parent with
    | false =>
        change ActivePathInput.incomingEdge graph m path.nodes (.observed parent) child = false at selected
        simp only [selected, Bool.false_and, Bool.false_eq_true, if_false, ite_self]
    | true =>
        have available := ofActivePath_parent_available path child parent selected
        change ActivePathInput.incomingEdge graph m path.nodes (.observed parent) child = true at selected
        simp only [available, selected, Bool.true_and, if_true]
  · apply foldl_congr
    intro total root
    rw [ofActivePath_rootMask]
    cases ActivePathInput.pairUsed graph path.nodes root <;>
      cases pairRootIncident graph.binary root child <;> cases cubeEnvironment graph point root <;> rfl

/-- Evaluate one actual internal row at every cube point.  Its own observed
bit occurs once, followed by exactly the original coordinates of the two
incoming neighbours.  The equality is derived from the real path masks and
their interpreter guards, not from an assumed row-evenness certificate. -/
theorem ofActivePath_rowPhase_internal_window
    (path : ActivePath graph m given (.observed source) (.observed target))
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (child : Fin S.count)
    (window : path.nodes = before ++ previous :: .observed child :: next :: after) (point : Cube graph) :
    ((ofActivePath path).rowPhase child).value point = Bool.xor (cubeSample graph point child)
      (Bool.xor (incomingValue graph m point previous child) (incomingValue graph m point next child)) := by
  rw [ofActivePath_actual_row]
  change Bool.xor (cubeSample graph point child)
    (Bool.xor
      ((List.finRange S.count).foldl (fun total parent => Bool.xor total
        (ActivePathInput.incomingEdge graph m path.nodes (.observed parent) child && cubeSample graph point parent)) false)
      ((List.finRange (pairRootCount graph)).foldl (fun total root => Bool.xor total
        (ActivePathInput.pairUsed graph path.nodes root && pairRootIncident graph root child &&
          cubeEnvironment graph point root)) false)) = _
  have observedReads : forall parent,
      (ActivePathInput.incomingEdge graph m path.nodes (.observed parent) child && cubeSample graph point parent) =
        Bool.xor (observedNeighborRead graph m point child previous parent)
          (observedNeighborRead graph m point child next parent) := by
    intro parent
    rw [ActivePathInput.incomingEdge_internal_window path.simple graph m before after previous next
      (.observed parent) child window]
    unfold observedNeighborRead
    cases SeparationNode.beq (.observed parent) previous <;> cases SeparationNode.beq (.observed parent) next <;>
      cases graph.expandedMutilatedEdge m (.observed parent) (.observed child) <;>
      cases cubeSample graph point parent <;> rfl
  have reservedReads : forall root,
      (ActivePathInput.pairUsed graph path.nodes root && pairRootIncident graph root child &&
        cubeEnvironment graph point root) = Bool.xor (reservedNeighborRead graph m point child previous root)
          (reservedNeighborRead graph m point child next root) := by
    intro root
    rw [ActivePathInput.pairUsed_incident_internal_window path before after previous next child window root]
    unfold reservedNeighborRead
    cases ActivePathInput.rootAt graph root previous <;> cases ActivePathInput.rootAt graph root next <;>
      cases graph.expandedMutilatedEdge m previous (.observed child) <;>
      cases graph.expandedMutilatedEdge m next (.observed child) <;>
      cases cubeEnvironment graph point root <;> rfl
  have observedFold := foldl_congr _ _ false (List.finRange S.count)
    (fun total parent => congrArg (Bool.xor total) (observedReads parent))
  have reservedFold := foldl_congr _ _ false (List.finRange (pairRootCount graph))
    (fun total root => congrArg (Bool.xor total) (reservedReads root))
  rw [observedFold, reservedFold, foldl_xor_pointwise, foldl_xor_pointwise]
  have previousMember : previous ∈ path.nodes := window ▸ List.mem_append_right before List.mem_cons_self
  have nextMember : next ∈ path.nodes := window ▸ List.mem_append_right before
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have previousInput := neighbor_folds path point child previous previousMember
  have nextInput := neighbor_folds path point child next nextMember
  rw [← previousInput, ← nextInput]
  congr 1
  have regroup (firstObserved secondObserved firstReserved secondReserved : Bool) :
      Bool.xor (Bool.xor firstObserved secondObserved) (Bool.xor firstReserved secondReserved) =
        Bool.xor (Bool.xor firstObserved firstReserved) (Bool.xor secondObserved secondReserved) := by
    cases firstObserved <;> cases secondObserved <;> cases firstReserved <;> cases secondReserved <;> rfl
  exact regroup _ _ _ _

/-- An omitted path row has no installed incoming input at all, so its
actual phase is exactly its own bit.  In particular an observed fork is
not silently required to be even: it is omitted from the interaction, and
may be odd in a useful direction.  This identity is valid on the full cube. -/
theorem ofActivePath_rowPhase_of_not_head
    (path : ActivePath graph m given (.observed source) (.observed target))
    (child : Fin S.count) (unselected : ActivePathInput.headRows graph m path.nodes child = false)
    (point : Cube graph) : ((ofActivePath path).rowPhase child).value point = cubeSample graph point child := by
  rw [ofActivePath_actual_row]
  have noObserved : forall parent,
      ActivePathInput.incomingEdge graph m path.nodes (.observed parent) child = false := by
    intro parent
    cases selected : ActivePathInput.incomingEdge graph m path.nodes (.observed parent) child with
    | false => rfl
    | true => exact False.elim (Bool.false_ne_true (unselected.symm.trans (ActivePathInput.incomingEdge_head selected)))
  have noReserved : forall root,
      (ActivePathInput.pairUsed graph path.nodes root && pairRootIncident graph.binary root child) = false := by
    intro root
    cases used : ActivePathInput.pairUsed graph path.nodes root with
    | false => exact Bool.false_and _
    | true =>
        cases incident : pairRootIncident graph.binary root child with
        | false => rfl
        | true => exact False.elim (Bool.false_ne_true (unselected.symm.trans
            (ActivePathInput.pairUsed_incident_head path root child used incident)))
  simp only [noObserved, noReserved, Bool.false_and]
  have observedZero : (List.finRange S.count).foldl (fun total _parent => Bool.xor total false) false = false :=
    foldl_unchanged _ _ _ (fun total _parent => Bool.xor_false total)
  have reservedZero : (List.finRange (pairRootCount graph.binary)).foldl (fun total _root => Bool.xor total false) false = false :=
    foldl_unchanged _ _ _ (fun total _root => Bool.xor_false total)
  rw [observedZero]
  calc
    _ = Bool.xor (cubeSample graph point child) (Bool.xor false false) :=
      congrArg (fun bit => Bool.xor (cubeSample graph point child) (Bool.xor false bit)) reservedZero
    _ = cubeSample graph point child := Bool.xor_false _

end LinearSignal
end HedgeChannelEnvironmentInstallation

end Causality
end Thesis
