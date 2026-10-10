import Thesis.CausalTransport.ActivePathDirection
import Thesis.CausalTransport.HedgeChannelPathRows

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction

/-!
# Construct the supported odd direction of an actual incoming path signal

The direction is explicit Type-level data: all original reserved-root bits
are true, the source and actual observed colliders are false, and the other
observed path bits are true.  Off-path observed bits are false.  Unused roots
are harmless free coordinates; no new common switch or globally readable
input is added to any installed mechanism.

The graph layer proves conditioning support and that every actual incoming
observed input is true.  A latent neighbour reads its actual original root,
which is also true.  The full-cube local-row identities then prove individual
parities: the incoming source is odd; every other selected head is even.
An omitted fork or outgoing endpoint can still have an odd own row and is
not smuggled into the selected interaction.

This discharges the path-signal direction obligation.  It does not install
the collider activation traces, route every mandatory Small row, or transfer
the odd source to a genuine Small approach when the pivot is outside Small.
Those remain the load-bearing universal conditional-completeness tasks.
-/

variable {S : ObservedSignature.{0}}

namespace HedgeChannelEnvironmentInstallation
namespace LinearSignal

variable {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
  {source target : Fin S.count}

/-- An explicit cube direction at the original input coordinates.  Its
definition needs no first-edge or parity flag; the first incoming arrow is
used only to prove that this direction has the required selected parities. -/
def activePathDirection (path : ActivePath graph m given (.observed source) (.observed target)) : Cube graph :=
  joinCube graph (fun _ => true) (fun child => ActivePathInput.nonColliderBits graph m path.nodes source child)

/-- The direction has exactly the declared observed mask at every node. -/
theorem activePathDirection_sample
    (path : ActivePath graph m given (.observed source) (.observed target)) (child : Fin S.count) :
    cubeSample graph (activePathDirection path) child = ActivePathInput.nonColliderBits graph m path.nodes source child := by
  rw [activePathDirection, cubeSample_joinCube]

/-- Every real reserved input is true, including an unused input which
remains free on the conditioning cylinder.  This does not make it readable
by a row whose actual incidence or path mask excludes it. -/
theorem activePathDirection_environment
    (path : ActivePath graph m given (.observed source) (.observed target)) (root : Fin (pairRootCount graph.binary)) :
    cubeEnvironment graph (activePathDirection path) root = true := by
  rw [activePathDirection, cubeEnvironment_joinCube]

/-- The direction is supported on the complete false conditioning
cylinder, also with the source fixed to false.  Every original reserved
coordinate remains in that cylinder; no input slice is discarded. -/
theorem activePathDirection_member
    (path : ActivePath graph m given (.observed source) (.observed target)) :
    activePathDirection path ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union given (NodeSet.singleton source))) := by
  rw [FiniteProduct.BooleanBlocks.cylinder_member_iff]
  simp only [cubeMask, activePathDirection, joinCube, FiniteProduct.BooleanBlocks.leftBlock_join,
    FiniteProduct.BooleanBlocks.rightBlock_join]
  constructor
  · rw [FiniteProduct.falseCylinderEnumeration_member_iff]
    intro root impossible
    cases impossible
  · rw [FiniteProduct.falseCylinderEnumeration_member_iff]
    intro child fixed
    rcases Bool.or_eq_true_iff.mp fixed with conditioned | atSource
    · exact ActivePathInput.nonColliderBits_condition_false path child conditioned
    · have equal := (NodeSet.singleton_eq_true_iff source child).mp atSource
      subst child
      exact ActivePathInput.nonColliderBits_source graph m path.nodes source

/-- An actual incoming neighbour contributes true at this direction.
Observed inputs use proved path noncollider/source facts; latent inputs use
their original reserved coordinate, not an assumed common input value. -/
theorem activePathDirection_incomingValue
    (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest)
    (firstIncoming : graph.expandedMutilatedEdge m first (.observed source) = true)
    (neighbor : SeparationNode S) (child : Fin S.count)
    (incoming : ActivePathInput.incomingEdge graph m path.nodes neighbor child = true) :
    incomingValue graph m (activePathDirection path) neighbor child = true := by
  have entries := Bool.and_eq_true_iff.mp incoming
  unfold incomingValue
  rw [entries.2, Bool.true_and]
  cases neighbor with
  | observed parent =>
      change cubeSample graph (activePathDirection path) parent = true
      rw [activePathDirection_sample]
      exact ActivePathInput.nonColliderBits_incoming_parent path first rest shape firstIncoming parent child incoming
  | latentPair left right =>
      have member := (ActivePathInput.stepOnPath_members entries.1).1
      have edge := path.latentPair_is_bidirected left right member
      change (if edge : graph.bidirected left right = true then
        cubeEnvironment graph (activePathDirection path) (pairRootBetween graph edge) else false) = true
      rw [dif_pos edge]
      exact activePathDirection_environment path _

/-- On any actual consecutive pair, the incoming contribution is exactly
its kept-arrow bit.  Outgoing neighbours contribute zero, rather than being
asserted to have a suitable coordinate value for an unavailable read. -/
theorem activePathDirection_incomingValue_eq_edge
    (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest)
    (firstIncoming : graph.expandedMutilatedEdge m first (.observed source) = true)
    (neighbor : SeparationNode S) (child : Fin S.count)
    (step : ActivePathInput.stepOnPath neighbor (.observed child) path.nodes = true) :
    incomingValue graph m (activePathDirection path) neighbor child =
      graph.expandedMutilatedEdge m neighbor (.observed child) := by
  cases edge : graph.expandedMutilatedEdge m neighbor (.observed child) with
  | false => simp only [incomingValue, edge, Bool.false_and]
  | true =>
      exact activePathDirection_incomingValue path first rest shape firstIncoming neighbor child
        (Bool.and_eq_true_iff.mpr ⟨step, edge⟩)

/-- The first incoming edge selects the source and makes its actual row
odd: the source's own bit is false and its one genuine incoming input is
true.  Neither row oddness nor head membership is supplied as a premise. -/
theorem activePathDirection_source_odd
    (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest)
    (firstIncoming : graph.expandedMutilatedEdge m first (.observed source) = true) :
    ActivePathInput.headRows graph m path.nodes source = true ∧
      ((ofActivePath path).rowPhase source).value (activePathDirection path) = true := by
  have step : ActivePathInput.stepOnPath first (.observed source) path.nodes = true := by
    rw [shape]
    exact (ActivePathInput.stepOnPath_first_pair (.observed source) first first rest (shape ▸ path.simple)).mpr rfl
  have incoming := Bool.and_eq_true_iff.mpr ⟨step, firstIncoming⟩
  refine ⟨ActivePathInput.incomingEdge_head incoming, ?_⟩
  rw [ofActivePath_rowPhase_first_pair path first rest shape, activePathDirection_sample,
    ActivePathInput.nonColliderBits_source,
    activePathDirection_incomingValue path first rest shape firstIncoming first source incoming]
  rfl

private theorem activePathDirection_internal_even
    (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest)
    (firstIncoming : graph.expandedMutilatedEdge m first (.observed source) = true)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S) (child : Fin S.count)
    (window : path.nodes = before ++ previous :: .observed child :: next :: after)
    (different : child ≠ source) (selected : ActivePathInput.headRows graph m path.nodes child = true) :
    ((ofActivePath path).rowPhase child).value (activePathDirection path) = false := by
  have previousStep := (ActivePathInput.stepOnPath_internal_window path.simple before after previous (.observed child) next previous window).mpr
    (Or.inl rfl)
  have nextStep := (ActivePathInput.stepOnPath_internal_window path.simple before after previous (.observed child) next next window).mpr
    (Or.inr rfl)
  have member : .observed child ∈ path.nodes := window ▸ List.mem_append_right before (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [ofActivePath_rowPhase_internal_window path before after previous next child window,
    activePathDirection_sample, ActivePathInput.nonColliderBits_of_mem graph m path.nodes source child member different,
    ActivePathInput.colliderRows_internal_window path.simple before after previous next child window,
    activePathDirection_incomingValue_eq_edge path first rest shape firstIncoming previous child previousStep,
    activePathDirection_incomingValue_eq_edge path first rest shape firstIncoming next child nextStep]
  rw [ActivePathInput.headRows_internal_window path.simple before after previous next child window] at selected
  unfold isColliderBool
  cases left : graph.expandedMutilatedEdge m previous (.observed child) <;>
    cases right : graph.expandedMutilatedEdge m next (.observed child)
  · rw [left, right] at selected
    cases selected
  · rfl
  · rfl
  · rfl

private theorem last_pair_of_distinct
    (path : ActivePath graph m given (.observed source) (.observed target)) (distinct : source ≠ target) :
    Exists fun before : List (SeparationNode S) => Exists fun previous : SeparationNode S =>
      path.nodes = before ++ [previous, .observed target] := by
  cases shape : path.nodes.reverse with
  | nil =>
      have starts := path.reverse.starts
      change path.nodes.reverse.head? = some (.observed target) at starts
      rw [shape] at starts
      cases starts
  | cons last tail =>
      have starts := path.reverse.starts
      change path.nodes.reverse.head? = some (.observed target) at starts
      rw [shape] at starts
      have equal := Option.some.inj starts
      subst last
      cases tail with
      | nil =>
          have finishes := path.reverse.finishes
          change path.nodes.reverse.getLast? = some (.observed source) at finishes
          rw [shape] at finishes
          exact False.elim (distinct (SeparationNode.observed.inj (Option.some.inj finishes)).symm)
      | cons previous rest =>
          refine ⟨rest.reverse, previous, ?_⟩
          have reversed := congrArg List.reverse shape
          simpa only [List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.append_assoc,
            List.cons_append, List.nil_append] using reversed

private theorem activePathDirection_target_even
    (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest)
    (firstIncoming : graph.expandedMutilatedEdge m first (.observed source) = true)
    (distinct : source ≠ target) (selected : ActivePathInput.headRows graph m path.nodes target = true) :
    ((ofActivePath path).rowPhase target).value (activePathDirection path) = false := by
  rcases last_pair_of_distinct path distinct with ⟨before, previous, lastShape⟩
  have reversedShape : path.nodes.reverse = .observed target :: previous :: before.reverse := by
    rw [lastShape]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append]
  have reversedHead : ActivePathInput.headRows graph m path.nodes.reverse target = true := by
    simpa only [ActivePathInput.headRows, ActivePathInput.incomingEdge,
      ActivePathInput.stepOnPath_reverse, List.any_reverse] using selected
  rw [reversedShape, ActivePathInput.headRows_first_pair graph m target previous before.reverse
    (reversedShape ▸ path.reverse.simple)] at reversedHead
  have step : ActivePathInput.stepOnPath previous (.observed target) path.nodes = true := by
    apply (ActivePathInput.stepOnPath_eq_true_iff _ _ _).mpr
    exact ⟨before, [], Or.inl lastShape⟩
  have incoming := Bool.and_eq_true_iff.mpr ⟨step, reversedHead⟩
  rw [ofActivePath_rowPhase_last_pair path before previous lastShape, activePathDirection_sample,
    ActivePathInput.nonColliderBits_target path distinct,
    activePathDirection_incomingValue path first rest shape firstIncoming previous target incoming]
  rfl

/-- Every selected head other than the source is even in the explicit
supported direction.  This covers arbitrary internal chains and colliders,
and an incoming target.  A fork or outgoing target is correctly omitted;
its potentially odd own row is not a background-evenness obligation. -/
theorem activePathDirection_selected_even
    (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest)
    (firstIncoming : graph.expandedMutilatedEdge m first (.observed source) = true)
    (child : Fin S.count)
    (selected : ActivePathInput.headRows graph m path.nodes child = true) (different : child ≠ source) :
    ((ofActivePath path).rowPhase child).value (activePathDirection path) = false := by
  have distinct := ActivePathInput.endpoints_ne_first_pair path first rest shape
  by_cases atTarget : child = target
  · subst child
    exact activePathDirection_target_even path first rest shape firstIncoming distinct selected
  · have member := ActivePathInput.headRows_member selected
    rcases exists_internal_neighbors_of_mem path.starts path.finishes member
      (fun same => different (SeparationNode.observed.inj same))
      (fun same => atTarget (SeparationNode.observed.inj same)) with
        ⟨before, previous, next, after, window⟩
    exact activePathDirection_internal_even path first rest shape firstIncoming before after previous next child window different selected

/-- The selected-row parity function is exactly the source indicator.
This retains omitted rows as zero contributions even when their own phase
is odd, and identifies the source as the unique odd selected row. -/
theorem activePathDirection_selected_row
    (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest)
    (firstIncoming : graph.expandedMutilatedEdge m first (.observed source) = true)
    (child : Fin S.count) :
    (if ActivePathInput.headRows graph m path.nodes child then
      ((ofActivePath path).rowPhase child).value (activePathDirection path) else false) = decide (child = source) := by
  by_cases atSource : child = source
  · subst child
    have odd := activePathDirection_source_odd path first rest shape firstIncoming
    rw [odd.1, if_pos rfl, odd.2, decide_eq_true rfl]
  · rw [decide_eq_false atSource]
    cases head : ActivePathInput.headRows graph m path.nodes child with
    | false => rfl
    | true =>
        change ((ofActivePath path).rowPhase child).value (activePathDirection path) = false
        exact activePathDirection_selected_even path first rest shape firstIncoming child head atSource

/-- The actual entire head interaction is odd on the supported direction.
Each selected row is counted once in the original ascending enumeration,
so the unique odd source contribution cannot cancel or be dropped.  This
is not yet oddness of a possibly different mandatory Small forest. -/
theorem activePathDirection_forest_odd
    (path : ActivePath graph m given (.observed source) (.observed target))
    (first : SeparationNode S) (rest : List (SeparationNode S))
    (shape : path.nodes = .observed source :: first :: rest)
    (firstIncoming : graph.expandedMutilatedEdge m first (.observed source) = true) :
    ((ofActivePath path).forestPhase (ActivePathInput.headRows graph m path.nodes)).value (activePathDirection path) = true := by
  rw [forestPhase_value, NodeSet.members, List.foldl_filter]
  change (List.finRange S.count).foldl (fun total child =>
    if ActivePathInput.headRows graph m path.nodes child then
      Bool.xor total (((ofActivePath path).rowPhase child).value (activePathDirection path)) else total) false = true
  have actualFold :
      (List.finRange S.count).foldl (fun total child =>
        if ActivePathInput.headRows graph m path.nodes child then
          Bool.xor total (((ofActivePath path).rowPhase child).value (activePathDirection path)) else total) false =
        (List.finRange S.count).foldl (fun total child => Bool.xor total (decide (child = source))) false := by
    apply foldl_congr
    intro total child
    have parity := activePathDirection_selected_row path first rest shape firstIncoming child
    cases selected : ActivePathInput.headRows graph m path.nodes child with
    | false =>
        rw [selected] at parity
        change false = _ at parity
        rw [← parity, Bool.xor_false]
        rfl
    | true =>
        rw [selected] at parity
        change ((ofActivePath path).rowPhase child).value (activePathDirection path) = _ at parity
        rw [← parity]
        rfl
  rw [actualFold]
  have sourceCount := basisAssignment_masked_foldl S.count source (fun _ => true)
  simpa only [if_true, basisAssignment] using sourceCount

end LinearSignal
end HedgeChannelEnvironmentInstallation

end Causality
end Thesis
