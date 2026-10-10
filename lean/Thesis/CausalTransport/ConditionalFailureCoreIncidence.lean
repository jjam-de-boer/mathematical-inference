import Thesis.CausalTransport.ConditionalFailureForkIncidence

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

/-!
# Actual activation and original-root columns of the completed installation

The fork incidence theorem and the ordinary proper-approach theorem already
identify two families of genuine two-row columns.  The remaining core must
not be treated as a guessed abstract linear graph.  Here the actual installed
activation and reserved-root masks supply two more families, on the same full
original input cube and with the same complete selected-row union.

A selected activation vertex can occur on the normalized path only as an
internal collider.  It consequently has no outgoing path-parent read, even
when it is also a path head.  Activation fusion supplies only its common
successor read.  The later all-Small policy stops at every completed core
vertex, so it cannot cancel or duplicate that trace column.  At an actual
unconditioned trace vertex the column is its own row XOR its genuine shared
successor row.  Merged incoming branches do not create an extra outgoing read.

An original reserved pair root is never replaced by a global switching bit.
Its path occurrence selects its two genuinely incident observed children;
both are original heads and survive in the core.  Both absorption layers
preserve exactly those reads and add none elsewhere.  A used root therefore
has its original two-child column, while an unused root has a zero column.
Every original root basis is supported, including roots incident to fixed
observed coordinates: conditioning an observation does not fix its root.

These are actual column and support theorems, not a supplied balance matrix
or a universal conditional countermodel.  The global incidence connectivity
to an original Small source and its successful supported direction remain to
be constructed, together with the ordinary noncollider path-head columns.
-/

namespace ConditionalBackdoorPathNormalForm

variable {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

/-! ## Actual trace columns survive both installations -/

/-- Every actual retained trace row is already a completed core row.
The inclusion concerns the pruned complete-trace union, not the larger
auxiliary activation-policy domain. -/
theorem activationTraceNodes_subset_core :
    NodeSet.Subset (normal.activationTraceNodes pivot forest) (normal.smallInteractionRows pivot forest) :=
  fun node selected => NodeSet.subset_union_left _ _ node (NodeSet.subset_union_right _ _ node selected)

/-- A trace vertex has no outgoing original path-parent read.  If a
read existed, actual adjacency would place it on the path; the proved
trace/path intersection would make it a collider, contradicting that arrow. -/
theorem activationTrace_path_parent_absent (parent row : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest parent = true) :
    ActivePathInput.incomingEdge graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton pivot.node))
      normal.cutPath.nodes (.observed parent) row = false := by
  apply Bool.eq_false_iff.mpr
  intro read
  have onPath := (ActivePathInput.stepOnPath_members (Bool.and_eq_true_iff.mp read).1).1
  have collider := (normal.activationTraceNodes_intersection_iff_collider pivot forest parent onPath).mp selected
  have absent := ActivePathInput.incoming_observed_parent_not_collider normal.cutPath parent row read
  exact Bool.false_ne_true (absent.symm.trans collider)

/-- The fused signal's complete observed column at a retained trace
vertex contains only its shared successor read.  Both original-head and
activation-only receiving rows use the same actual entry. -/
theorem activationInteraction_trace_parent_mask (parent row : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest parent = true) :
    (normal.activationInteractionSignal pivot forest).parentMask row parent =
      decide (normal.activationTraceSuccessor pivot forest parent = some row) := by
  have absent := normal.activationTrace_path_parent_absent pivot forest parent row selected
  cases head : normal.pathHeads row <;>
    simp only [activationInteractionSignal, LinearSignal.absorbSuccessor, head,
      Bool.false_eq_true, if_false, if_true, LinearSignal.ofActivePath, absent, Bool.false_xor]

/-- The later mandatory-source policy is stopped at this actual core
vertex.  It cannot introduce a second trace continuation or delete the
first one at an overlapping Small/core receiving row. -/
theorem forkAbsorbedInteraction_trace_parent_mask (parent row : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest parent = true) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).parentMask row parent =
      decide (normal.activationTraceSuccessor pivot forest parent = some row) := by
  have stopped := normal.forkAbsorptionSuccessor_stops_core boundary pivot forest parent
    (normal.activationTraceNodes_subset_core pivot forest parent selected)
  have original := normal.activationInteraction_trace_parent_mask pivot forest parent row selected
  cases core : normal.smallInteractionRows pivot forest row with
  | true =>
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core, if_true,
        original, stopped, reduceCtorEq, decide_false, Bool.xor_false]
  | false =>
      have noExit : normal.activationTraceSuccessor pivot forest parent ≠ some row := by
        intro edge
        have destination := (childWellFormed_edge _ _ (normal.activationTraceSuccessor_wellFormed pivot forest) edge).2.1
        have present := normal.activationTraceNodes_subset_core pivot forest row destination
        exact Bool.false_ne_true (core.symm.trans present)
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core,
        Bool.false_eq_true, if_false, stopped, reduceCtorEq, decide_false, decide_eq_false noExit]

/-- The actual trace column includes the own bit exactly once and the
unique shared successor entry.  The declared-edge guard is discharged only
when that actual successor exists; sinks have just their own entry. -/
theorem forkAbsorbedInteraction_trace_coefficient (parent row : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest parent = true) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).observedRowCoefficient row parent =
      Bool.xor (decide (row = parent))
        (decide (normal.activationTraceSuccessor pivot forest parent = some row)) := by
  rw [LinearSignal.observedRowCoefficient,
    normal.forkAbsorbedInteraction_trace_parent_mask boundary pivot forest parent row selected]
  by_cases edge : normal.activationTraceSuccessor pivot forest parent = some row
  · have declared := (childWellFormed_edge _ _ (normal.activationTraceSuccessor_wellFormed pivot forest) edge).2.2
    rw [declared, Bool.true_and]
  · rw [decide_eq_false edge, Bool.and_false]

/-- At a real transmitting trace vertex the full-cube basis has exactly
the own-row/successor-row pair.  No trace disjointness or precomputed sparse
matrix is assumed, and the successor may be a merged branch vertex. -/
theorem activationTrace_basis_pair {parent next : Fin S.count}
    (selected : normal.activationTraceNodes pivot forest parent = true)
    (edge : normal.activationTraceSuccessor pivot forest parent = some next) (row : Fin S.count) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
      (basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent)) =
      Bool.xor (decide (row = parent)) (decide (row = next)) := by
  rw [LinearSignal.rowPhase_observed_basis,
    normal.forkAbsorbedInteraction_trace_coefficient boundary pivot forest parent row selected, edge]
  simp only [Option.some.injEq, eq_comm]

/-- Every transmitting trace coordinate avoids the complete original
action and condition selection.  Selected action avoidance is inherited;
condition avoidance is derived from the actual sink classifier. -/
theorem activationTrace_transmitter_fixed_free {parent next : Fin S.count}
    (selected : normal.activationTraceNodes pivot forest parent = true)
    (edge : normal.activationTraceSuccessor pivot forest parent = some next) :
    NodeSet.union query.action query.condition parent = false := by
  have action := normal.activationTraceNodes_action_free pivot forest parent selected
  have condition : query.condition parent = false := by
    apply Bool.eq_false_iff.mpr
    intro conditioned
    have stopped := (normal.activationTraceSuccessor_sink_iff_condition pivot forest parent selected).mpr conditioned
    rw [edge] at stopped
    cases stopped
  rw [NodeSet.union, action, condition]
  rfl

/-- Every actual unconditioned trace row has a genuine, selected,
distinct successor.  The existential is used in Prop only; later executable
route construction reads the existing shared successor map directly. -/
theorem activationTrace_unconditioned_successor (parent : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest parent = true)
    (unconditioned : query.condition parent = false) :
    Exists fun next : Fin S.count =>
      normal.activationTraceSuccessor pivot forest parent = some next ∧
        normal.activationTraceNodes pivot forest next = true ∧ parent ≠ next := by
  cases result : normal.activationTraceSuccessor pivot forest parent with
  | none =>
      have conditioned := (normal.activationTraceSuccessor_sink_iff_condition pivot forest parent selected).mp result
      exact False.elim (Bool.false_ne_true (unconditioned.symm.trans conditioned))
  | some next =>
      have actual := childWellFormed_edge _ _ (normal.activationTraceSuccessor_wellFormed pivot forest) result
      exact ⟨next, rfl, actual.2.1, fun same => Nat.ne_of_lt (S.directed_earlier actual.2.2) (congrArg Fin.val same)⟩

/-- The actual two-row trace direction belongs to the whole unchanged
original evidence cylinder.  Conditioned sinks are not silently offered as
free coordinates: this theorem requires a genuine transmitting edge. -/
theorem activationTrace_basis_supported {parent next : Fin S.count}
    (selected : normal.activationTraceNodes pivot forest parent = true)
    (edge : normal.activationTraceSuccessor pivot forest parent = some next) :
    basisAssignment (pairRootCount graph.binary + S.count) (Fin.natAdd (pairRootCount graph.binary) parent) ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) := by
  apply (basisAssignment_member_iff _ _ _).mpr
  change FiniteProduct.BooleanBlocks.rightBlock (pairRootCount graph.binary) S.count
    (cubeMask graph (NodeSet.union query.action query.condition)) parent = false
  rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join]
  exact normal.activationTrace_transmitter_fixed_free pivot forest selected edge

/-- Both rows of an actual transmitting trace column survive in the
complete installed union.  Arbitrary Small overlap retains them once; an
edge never points at a row omitted by the completed interaction. -/
theorem activationTrace_pair_rows_selected {parent next : Fin S.count}
    (selected : normal.activationTraceNodes pivot forest parent = true)
    (edge : normal.activationTraceSuccessor pivot forest parent = some next) :
    normal.forkAbsorbedInteractionRows boundary pivot forest parent = true ∧
      normal.forkAbsorbedInteractionRows boundary pivot forest next = true := by
  have destination := (childWellFormed_edge _ _ (normal.activationTraceSuccessor_wellFormed pivot forest) edge).2.1
  exact ⟨NodeSet.subset_union_left _ _ parent (normal.activationTraceNodes_subset_core pivot forest parent selected),
    NodeSet.subset_union_left _ _ next (normal.activationTraceNodes_subset_core pivot forest next destination)⟩

/-! ## Original pair-root columns are preserved, not globally shared -/

/-- Activation fusion preserves the complete original path-root mask,
including its zeros.  A genuinely used incident root already selects its
receiving head, so no true read is lost at an activation-only row. -/
theorem activationInteraction_root_mask (row : Fin S.count) (root : Fin (pairRootCount graph.binary)) :
    (normal.activationInteractionSignal pivot forest).rootMask row root =
      (ActivePathInput.pairUsed graph normal.cutPath.nodes root && pairRootIncident graph.binary root row) := by
  have original := LinearSignal.ofActivePath_rootMask normal.cutPath row root
  cases head : normal.pathHeads row with
  | true => simp only [activationInteractionSignal, LinearSignal.absorbSuccessor, head, if_true, original]
  | false =>
      have zero : (ActivePathInput.pairUsed graph normal.cutPath.nodes root && pairRootIncident graph.binary root row) = false := by
        apply Bool.eq_false_iff.mpr
        intro read
        have parts := Bool.and_eq_true_iff.mp read
        have present := ActivePathInput.pairUsed_incident_head normal.cutPath root row parts.1 parts.2
        exact Bool.false_ne_true (head.symm.trans present)
      simp only [activationInteractionSignal, LinearSignal.absorbSuccessor, head, Bool.false_eq_true, if_false, zero]

/-- The all-Small absorber preserves precisely the same original-root
mask.  Its new approach-only rows do not gain access to any reserved input;
every genuine used incident row was already in the completed core. -/
theorem forkAbsorbedInteraction_root_mask (row : Fin S.count) (root : Fin (pairRootCount graph.binary)) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).rootMask row root =
      (ActivePathInput.pairUsed graph normal.cutPath.nodes root && pairRootIncident graph.binary root row) := by
  have original := normal.activationInteraction_root_mask pivot forest row root
  cases core : normal.smallInteractionRows pivot forest row with
  | true => simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core, if_true, original]
  | false =>
      have zero : (ActivePathInput.pairUsed graph normal.cutPath.nodes root && pairRootIncident graph.binary root row) = false := by
        apply Bool.eq_false_iff.mpr
        intro read
        have parts := Bool.and_eq_true_iff.mp read
        have head := ActivePathInput.pairUsed_incident_head normal.cutPath root row parts.1 parts.2
        have present : normal.smallInteractionRows pivot forest row = true :=
          NodeSet.subset_union_left _ _ row (NodeSet.subset_union_left _ _ row head)
        exact Bool.false_ne_true (core.symm.trans present)
      simp only [forkAbsorbedInteractionSignal, LinearSignal.absorbSuccessor, core, Bool.false_eq_true, if_false, zero]

/-- The actual interpreter's root coefficient is the original occurrence
test times its genuine incidence.  Its local incidence guard is retained
and proved redundant here, not disabled in the installed mechanism. -/
theorem forkAbsorbedInteraction_root_coefficient (row : Fin S.count) (root : Fin (pairRootCount graph.binary)) :
    (normal.forkAbsorbedInteractionSignal boundary pivot forest).rootRowCoefficient row root =
      (ActivePathInput.pairUsed graph normal.cutPath.nodes root && pairRootIncident graph.binary root row) := by
  rw [LinearSignal.rootRowCoefficient, normal.forkAbsorbedInteraction_root_mask boundary pivot forest row root]
  cases ActivePathInput.pairUsed graph normal.cutPath.nodes root <;>
    cases pairRootIncident graph.binary root row <;> rfl

/-- A used original root has two actual core children.  Their head
membership comes from genuine path/root adjacency, not from an arbitrary
incidence label attached to a proposed abstract column. -/
theorem originalRoot_children_in_core (root : Fin (pairRootCount graph.binary))
    (used : ActivePathInput.pairUsed graph normal.cutPath.nodes root = true) :
    normal.smallInteractionRows pivot forest ((pairRoots graph.binary).get root).1 = true ∧
      normal.smallInteractionRows pivot forest ((pairRoots graph.binary).get root).2 = true := by
  have leftIncident : pairRootIncident graph.binary root ((pairRoots graph.binary).get root).1 = true := by
    simp only [pairRootIncident, decide_true, Bool.true_or]
  have rightIncident : pairRootIncident graph.binary root ((pairRoots graph.binary).get root).2 = true := by
    simp only [pairRootIncident, decide_true, Bool.or_true]
  have left := ActivePathInput.pairUsed_incident_head normal.cutPath root _ used leftIncident
  have right := ActivePathInput.pairUsed_incident_head normal.cutPath root _ used rightIncident
  exact ⟨NodeSet.subset_union_left _ _ _ (NodeSet.subset_union_left _ _ _ left),
    NodeSet.subset_union_left _ _ _ (NodeSet.subset_union_left _ _ _ right)⟩

-- The original enumeration is ordered, so its two children are distinct.
-- Converting OR incidence to XOR requires that fact; it would be false for
-- an invented root with a repeated endpoint or arbitrary global incidence.
private theorem original_root_incidence_pair (root : Fin (pairRootCount graph.binary)) (row : Fin S.count) :
    pairRootIncident graph.binary root row = Bool.xor
      (decide (row = ((pairRoots graph.binary).get root).1))
      (decide (row = ((pairRoots graph.binary).get root).2)) := by
  have ordered := (pairRoots_get_spec graph.binary root).1
  have distinct : ((pairRoots graph.binary).get root).1 ≠ ((pairRoots graph.binary).get root).2 := by
    intro same
    have values := congrArg Fin.val same
    rw [values] at ordered
    exact Nat.lt_irrefl _ ordered
  change (decide (row = ((pairRoots graph.binary).get root).1) ||
    decide (row = ((pairRoots graph.binary).get root).2)) = _
  by_cases left : row = ((pairRoots graph.binary).get root).1
  · have right : row ≠ ((pairRoots graph.binary).get root).2 := fun same => distinct (left.symm.trans same)
    rw [decide_eq_true left, decide_eq_false right]
    rfl
  · by_cases right : row = ((pairRoots graph.binary).get root).2
    · rw [decide_eq_false left, decide_eq_true right]
      rfl
    · rw [decide_eq_false left, decide_eq_false right]
      rfl

/-- A used original pair root has exactly its two genuine child row
incidences on the full cube.  Reversed expanded aliases use this same root
index; neither fusion nor all-Small routing creates a third reserved read. -/
theorem originalRoot_basis_pair (root : Fin (pairRootCount graph.binary))
    (used : ActivePathInput.pairUsed graph normal.cutPath.nodes root = true) (row : Fin S.count) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
      (basisAssignment (pairRootCount graph.binary + S.count) (root.castAdd S.count)) =
      Bool.xor (decide (row = ((pairRoots graph.binary).get root).1))
        (decide (row = ((pairRoots graph.binary).get root).2)) := by
  rw [LinearSignal.rowPhase_root_basis,
    normal.forkAbsorbedInteraction_root_coefficient boundary pivot forest row root, used, Bool.true_and]
  exact original_root_incidence_pair root row

/-- Every original root basis is supported under the complete original
action and condition mask.  Even a root incident to a conditioned observed
row remains independent and free; only that observation's bit is fixed. -/
theorem originalRoot_basis_supported (root : Fin (pairRootCount graph.binary)) :
    basisAssignment (pairRootCount graph.binary + S.count) (root.castAdd S.count) ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) := by
  apply (basisAssignment_member_iff _ _ _).mpr
  change FiniteProduct.BooleanBlocks.leftBlock (pairRootCount graph.binary) S.count
    (cubeMask graph (NodeSet.union query.action query.condition)) root = false
  rw [cubeMask, FiniteProduct.BooleanBlocks.leftBlock_join]

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
