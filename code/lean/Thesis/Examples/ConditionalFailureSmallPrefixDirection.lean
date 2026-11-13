import Thesis.Examples.ConditionalFailureSmallPrefixDirectionGraph

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureSmallPrefixDirection

open Probability PathSpecification FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# Transfer an outside-Small pivot through the actual proper prefix

The companion's real hedge has Small `U,R`, while its first conditioner `P`
is outside Small.  The actual normalized path is `P <- Y`.  All-Small
absorption retains the real `U -> R -> P` policy and conserves the original
outcome character, but its initial path direction still leaves background
row `P` odd.  Merely proving whole-union conservation would not close the case.

We XOR that supported direction with the actual proper-prefix flip `U,R`.
Conditioned `P` and every original reserved input remain unchanged.  The two
boundary-source identity transfers the odd row to Small source `U`; `R` and
the actual outside-Small receiver `P` are even.  Full matching then derives
oddness of the complete mandatory Small phase.  The existing covariance
constructor supplies positive, observationally equal original-label models
with a gap in the unchanged conditional query.

This is a genuine outside-Small-pivot semantic instance, not the universal
transfer theorem.  In other graphs the original interaction can read a
proper-prefix fork.  The general prefix-row identity retains that residual,
which cannot be replaced by this example's zero value.
-/

private theorem source_in_small : witness.small source = true := by decide +kernel

/-- The finite receiving mask of the completed core.  `actual_core` below
proves equality to the actual normalized selection before conservation uses it. -/
def core : NodeSet signature := NodeSet.singleton pivotNode

private theorem receives : NodeSet.Subset query.condition core := fun _ selected => selected

private theorem no_colliders : normal.colliderSeeds = NodeSet.empty := by
  unfold ConditionalBackdoorPathNormalForm.colliderSeeds
  rw [normal_window]
  rfl

private theorem no_traces : normal.activationTraceNodes pivot forest = NodeSet.empty := by
  funext node
  change normal.activationTraceNodes pivot forest node = false
  apply Bool.eq_false_iff.mpr
  intro selected
  unfold ConditionalBackdoorPathNormalForm.activationTraceNodes at selected
  rcases List.any_eq_true.mp selected with ⟨seed, _member, _visited⟩
  have inside := (NodeSet.mem_members_iff _ _).mp seed.property
  have absent : normal.colliderSeeds seed.val = false := congrFun no_colliders seed.val
  rw [absent] at inside
  cases inside

/-- Derive the actual receiving selection from the proved normal window,
without reducing its exhaustive search or substituting a different signal. -/
theorem actual_core : normal.smallInteractionRows pivot forest = core := by
  unfold core ConditionalBackdoorPathNormalForm.smallInteractionRows
    ConditionalBackdoorPathNormalForm.activationInteractionRows ConditionalBackdoorPathNormalForm.pathHeads
  rw [normal_window, no_traces]
  funext child
  decide +kernel +revert

def prefixPath := boundary.absorbingPath core receives source source_in_small
def installedRows : NodeSet signature := NodeSet.union core (boundary.absorbingNodes core receives)
def installed : LinearSignal graph := (normal.activationInteractionSignal pivot forest).absorbSuccessor core
  (boundary.absorbingSuccessor core receives)
def background : NodeSet signature := NodeSet.diff installedRows witness.small

/-- Use the actual computed prefix, not a literal direction mask supplied
to the semantic theorem.  The original direction and alphabet are retained. -/
def direction : Cube graph := LinearSignal.shiftBySuccessorPrefix prefixPath normal.pathDirection

theorem actual_prefix_path : prefixPath.nodes = [source, commonRoot, pivotNode] := by
  decide +kernel

theorem actual_prefix_bits : prefixPath.prefixBits = NodeSet.union (NodeSet.singleton source) (NodeSet.singleton commonRoot) := by
  funext child
  unfold SuccessorPath.prefixBits SuccessorPath.bits
  rw [actual_prefix_path]
  decide +kernel +revert

private theorem prefix_fixed_free : forall child, child ∈ prefixPath.nodes -> child ≠ prefixPath.endpoint ->
    NodeSet.union query.action query.condition child = false := by
  rw [actual_prefix_path]
  decide +kernel

private theorem prefix_outcome_free : forall child, child ∈ prefixPath.nodes -> child ≠ prefixPath.endpoint ->
    NodeSet.singleton normal.outcome child = false := by
  have endpoint : normal.outcome = outcome := (NodeSet.singleton_eq_true_iff _ _).mp normal.outcome_selected
  rw [actual_prefix_path, endpoint]
  decide +kernel

theorem direction_supported : direction ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
    (cubeMask graph (NodeSet.union query.action query.condition)) :=
  LinearSignal.shiftBySuccessorPrefix_member prefixPath _ prefix_fixed_free normal.pathDirection normal.pathDirection_member

theorem outcome_odd : (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value direction = true := by
  rw [direction, LinearSignal.shiftBySuccessorPrefix_maskPhase prefixPath _ prefix_outcome_free]
  exact normal.activationInteraction_outcome_odd pivot

/-- The actual two-edge proper prefix has exactly its two boundary
sources in the shared forest.  The receiving evidence bit is not flipped. -/
theorem actual_prefix_two_boundaries (child : Fin signature.count) :
    hedgeRoutingLocalSource (boundary.absorbingSuccessor core receives) prefixPath.prefixBits child =
      Bool.xor (decide (child = source)) (decide (child = pivotNode)) := by
  have endpoint : prefixPath.endpoint = pivotNode := by decide +kernel
  simpa only [endpoint] using prefixPath.prefixBits_localSource child

/-- All original reserved coordinates are retained literally.  The
proper-prefix correction introduces no new common input and changes none. -/
theorem original_reserved_direction_retained : cubeEnvironment graph direction = cubeEnvironment graph normal.pathDirection := by
  funext root
  change Bool.xor (cubeEnvironment graph normal.pathDirection root)
    (cubeEnvironment graph (LinearSignal.successorPrefixDirection prefixPath) root) = _
  rw [LinearSignal.successorPrefixDirection_environment, Bool.xor_false]

/-- The uncorrected absorbed direction really leaves outside-Small `P`
odd.  This regression makes the transfer necessary, not cosmetic. -/
theorem initial_background_pivot_odd : background pivotNode = true ∧
    (installed.rowPhase pivotNode).value normal.pathDirection = true := by
  unfold background installedRows installed ConditionalBackdoorPathNormalForm.activationInteractionSignal
    ConditionalBackdoorPathNormalForm.pathHeads ConditionalBackdoorPathNormalForm.activationTraceSuccessor LinearSignal.ofActivePath
  rw [no_traces, normal_window]
  unfold ConditionalBackdoorPathNormalForm.pathDirection LinearSignal.activePathDirection
  rw [normal_window]
  decide +kernel

/-- Row computations below unfold only the legal masks and proved actual
path window; they never evaluate the normal-form search or any model table. -/
theorem background_even : forall child, background child = true -> (installed.rowPhase child).value direction = false := by
  unfold background installedRows installed
  unfold ConditionalBackdoorPathNormalForm.activationInteractionSignal ConditionalBackdoorPathNormalForm.pathHeads
    ConditionalBackdoorPathNormalForm.activationTraceSuccessor LinearSignal.ofActivePath
  rw [no_traces, normal_window]
  unfold direction LinearSignal.shiftBySuccessorPrefix
    ConditionalBackdoorPathNormalForm.pathDirection LinearSignal.activePathDirection
  rw [normal_window]
  decide +kernel

/-- The literal receiving mask was proved equal to the actual normalized
core.  Apply generic absorption conservation on it, avoiding any transport
of proof-bearing trace data through a mask rewrite. -/
private theorem full_matching (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    ((installed.forestPhase witness.small).xor (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome)))).value point =
      (selectedPhase _ signature.count background installed.rowPhase).value point := by
  have coverage : NodeSet.Subset witness.small installedRows := fun node inside =>
    NodeSet.subset_union_right _ _ node (boundary.small_subset_absorbingNodes core receives node inside)
  have partition : NodeSet.union witness.small background = installedRows := NodeSet.union_diff_eq coverage
  have whole : (installed.forestPhase installedRows).value point =
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point := by
    unfold installed installedRows
    rw [LinearSignal.absorbSuccessor_forestPhase _ _ _ _
      (boundary.absorbingSuccessor_wellFormed core receives)
      (boundary.absorbingSuccessor_stops core receives)
      (boundary.absorbingSinks_subset_interaction core receives), ← actual_core]
    exact normal.smallInteraction_conditionalPhase pivot forest point listed
  have conserved : Bool.xor ((installed.forestPhase witness.small).value point)
      ((selectedPhase _ signature.count background installed.rowPhase).value point) =
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point := by
    rw [LinearSignal.selectedPhase_value_eq_forestPhase,
      ← LinearSignal.forestPhase_union_of_disjoint installed witness.small background
        (NodeSet.disjoint_diff installedRows witness.small), partition]
    exact whole
  change Bool.xor ((installed.forestPhase witness.small).value point)
    ((maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point) = _
  rw [← conserved]
  generalize (installed.forestPhase witness.small).value point = smallBit
  generalize (selectedPhase _ signature.count background installed.rowPhase).value point = backgroundBit
  cases smallBit <;> cases backgroundBit <;> rfl

/-- Complete original-cylinder matching was already proved by all-Small
absorption; the supported direction supplies its remaining parity fields. -/
def parityWitness : ConditionalParityWitness witness installed installed := by
  have matching : forall point, point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) ->
      ((installed.forestPhase witness.small).xor (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome)))).value point =
        (selectedPhase _ signature.count background installed.rowPhase).value point :=
    full_matching
  have even := selectedPhase_value_eq_false_of_even _ _ background installed.rowPhase direction background_even
  have conserved := matching direction direction_supported
  change Bool.xor ((installed.forestPhase witness.small).value direction)
    ((maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value direction) = _ at conserved
  rw [outcome_odd, even] at conserved
  have smallOdd : (installed.forestPhase witness.small).value direction = true := by
    cases bit : (installed.forestPhase witness.small).value direction with
    | false => rw [bit] at conserved; cases conserved
    | true => rfl
  exact {
    outcomeMask := cubeMask graph (NodeSet.singleton normal.outcome)
    outcomeMask_member := normal.activationInteraction_outcome_mask_member pivot
    direction := direction
    direction_member := direction_supported
    small_odd := smallOdd
    outcome_odd := outcome_odd
    selected := background
    selected_outside_small := by
      intro child selected
      simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp selected).2
    selected_avoids_action := by
      intro child selected
      have retained := (Bool.and_eq_true_iff.mp selected).1
      rcases Bool.or_eq_true_iff.mp retained with receiving | absorbed
      · have selectedCore := actual_core.symm ▸ receiving
        exact normal.smallInteractionRows_action_free pivot forest child selectedCore
      · exact boundary.absorbingNodes_action_free core receives child absorbed
    selected_even := background_even
    matching := matching
  }

/-- Oddness now belongs to the whole genuine Small set, not to outside
pivot `P` or merely to the unpartitioned normalized interaction. -/
theorem complete_small_phase_odd : (installed.forestPhase witness.small).value direction = true := parityWitness.small_odd

/-- The general construction yields a fully positive original-alphabet
countermodel pair for a genuine outside-Small-pivot query. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfParity witness rich installed installed parityWitness

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

end CurrentConditionalFailureSmallPrefixDirection
end Examples
end Causality
end Thesis
