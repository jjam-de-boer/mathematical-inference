import Thesis.CausalTransport.ConditionalFailureSmallApproach

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}}

/-!
# Absorb every mandatory Small row at its first actual interaction contact

On the hard all-Small flow boundary, each original Small source has an actual
complete path ending at an original conditioner.  The completed normalized
interaction retains every such conditioner.  Thus every source reaches the
interaction, even when its first contact is an unconditioned path head or an
activation vertex rather than its eventual conditioned endpoint.

We truncate each existing path at its first interaction contact.  All paths
use the same stopped boundary-flow successor, and the transmitting domain is
the union of their complete truncated traces.  Shared suffixes and arbitrary
merges are allowed.  A source already in the interaction has a singleton
trace; an interaction row is never resumed and is never installed twice.
The finite scans below construct the path and domain data, while the proofs
derive complete Small coverage, closure, legal arrows and receiving sinks.

The final application absorbs this forest into the actual normalized signal.
Whole-cube conservation preserves its phase, hence its outcome character on
the full original action/condition cylinder.  No zero-tail premise is needed
for conservation.  This does not yet prove the required direction parities:
an omitted normalized-path fork can have a nonzero bit, and a first contact
can occur before the retained pivot.  Small oddness transfer and evenness of
all selected outside-Small rows remain genuine obligations, not fields
silently asserted by the absorption constructor.
-/

namespace HedgeWitness

variable {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator)

/-- Stop the one original boundary-flow policy at every receiving
interaction row.  The original query, hedge and arrows are unchanged. -/
def smallInteractionStopSuccessor (interaction : NodeSet S) : ForestChild S := fun parent =>
  if interaction parent then none else w.conditionalBoundarySuccessor parent

/-- Stopping transmitters retains well-formedness on the old flow domain.
The later pruning step separately proves that its smaller domain is closed. -/
theorem smallInteractionStopSuccessor_wellFormed (interaction : NodeSet S) :
    childWellFormedBool w.smallOutcomeFlowNodes (w.smallInteractionStopSuccessor interaction) = true := by
  apply List.all_eq_true.mpr
  intro parent member
  cases selected : interaction parent with
  | true =>
      cases w.smallOutcomeFlowNodes parent <;>
        simp only [smallInteractionStopSuccessor, selected, if_true]
  | false =>
      have old := (List.all_eq_true.mp w.conditionalBoundarySuccessor_wellFormed) parent member
      simpa only [smallInteractionStopSuccessor, selected, Bool.false_eq_true, if_false] using old

end HedgeWitness

namespace ConditionedSmallFlowBoundary

variable {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (interaction : NodeSet S)
    (receivesCondition : NodeSet.Subset query.condition interaction)

-- Unlike a newly searched graph route, this split retains the actual old
-- successor list.  The boundary's endpoint is conditioned, so the split
-- succeeds for every Small source without a guessed contact or sink flag.
private def firstInteraction (source : Fin S.count) (inside : w.small source = true) :
    ConditionalActivationRouting.FirstTargetPrefix interaction (w.conditionalBoundaryPath source inside).nodes :=
  ConditionalActivationRouting.firstTargetPrefix interaction
    (w.conditionalBoundaryPath source inside).endpoint
    (receivesCondition _ (FirstConditionedSmallApproach.ofBoundary boundary source inside).endpoint_condition)
    (w.conditionalBoundaryPath source inside).nodes (w.conditionalBoundaryPath source inside).finishes

-- Only proper prefix vertices transmit.  The receiving final vertex may
-- already have a boundary successor; the stopped policy intentionally omits it.
private theorem consecutive_stop (interaction : NodeSet S) (successor : ForestChild S) :
    forall before : List (Fin S.count), forall endpoint : Fin S.count,
      Consecutive (fun parent child => successor parent = some child) (before ++ [endpoint]) ->
      (forall node, node ∈ before -> interaction node = false) ->
      Consecutive (fun parent child =>
        (if interaction parent then none else successor parent) = some child) (before ++ [endpoint])
  | [], _, _, _ => True.intro
  | head :: tail, endpoint, directed, free => by
      have absent := free head (List.mem_cons.mpr (Or.inl rfl))
      cases tail with
      | nil =>
          exact ⟨by simpa only [absent, Bool.false_eq_true, if_false] using directed.1, True.intro⟩
      | cons next rest =>
          exact ⟨by simpa only [absent, Bool.false_eq_true, if_false] using directed.1,
            consecutive_stop interaction successor (next :: rest) endpoint directed.2
              (fun node member => free node (List.mem_cons.mpr (Or.inr member)))⟩

/-- Complete actual prefix from a mandatory Small source to its first
receiving row.  Its list comes from the existing boundary path, not from
eliminating an existential contact into data or searching a different route. -/
def interactionStopPath (source : Fin S.count) (inside : w.small source = true) :
    SuccessorPath w.smallOutcomeFlowNodes (w.smallInteractionStopSuccessor interaction) source := by
  let original := w.conditionalBoundaryPath source inside
  let first := boundary.firstInteraction interaction receivesCondition source inside
  have directed := Consecutive.prefix_append first.before first.target first.after
    (first.split ▸ original.consecutive)
  refine {
    nodes := first.before ++ [first.target]
    endpoint := first.target
    starts := ?_
    finishes := List.getLast?_concat
    simple := ?_
    consecutive := consecutive_stop interaction w.conditionalBoundarySuccessor first.before first.target directed first.before_free
    stopped := by simp only [HedgeWitness.smallInteractionStopSuccessor, first.selected, if_true]
    inside := ?_
  }
  · have starts := original.starts
    rw [first.split] at starts
    cases shape : first.before with
    | nil => simpa only [shape, List.nil_append, List.head?_cons] using starts
    | cons head tail => simpa only [shape, List.cons_append, List.head?_cons] using starts
  · apply Consecutive.nodup_of_fin_lt
    exact Consecutive.mono (fun _ _ edge => S.directed_earlier
      (childWellFormed_edge w.smallOutcomeFlowNodes w.conditionalBoundarySuccessor
        w.conditionalBoundarySuccessor_wellFormed edge).2.2) _ directed
  · intro node visited
    apply original.inside node
    rw [first.split]
    rcases List.mem_append.mp visited with before | endpoint
    · exact List.mem_append.mpr (Or.inl before)
    · have same := List.mem_singleton.mp endpoint
      subst node
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-- Every truncated path really ends in the receiving interaction,
including zero-edge contacts at an already selected Small source. -/
theorem interactionStopPath_endpoint_in_interaction (source : Fin S.count) (inside : w.small source = true) :
    interaction (boundary.interactionStopPath interaction receivesCondition source inside).endpoint = true :=
  (boundary.firstInteraction interaction receivesCondition source inside).selected

/-- The complete first-contact list is an actual prefix of the original
boundary list.  This membership contract keeps whole-route outcome freedom
available after truncation; it does not replace that freedom by endpoint data. -/
theorem interactionStopPath_subset_boundary (source : Fin S.count) (inside : w.small source = true)
    (node : Fin S.count) (visited : node ∈ (boundary.interactionStopPath interaction receivesCondition source inside).nodes) :
    node ∈ (w.conditionalBoundaryPath source inside).nodes := by
  let first := boundary.firstInteraction interaction receivesCondition source inside
  change node ∈ first.before ++ [first.target] at visited
  rw [first.split]
  rcases List.mem_append.mp visited with before | endpoint
  · exact List.mem_append.mpr (Or.inl before)
  · have same := List.mem_singleton.mp endpoint
    subst node
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-- Every proper vertex precedes the first receiving contact, even when
that contact is unconditioned.  Merely stopping at the eventual conditioner
would not establish this stronger interaction-prefix freedom. -/
theorem interactionStopPath_before_free (source : Fin S.count) (inside : w.small source = true)
    (node : Fin S.count) (visited : node ∈ (boundary.interactionStopPath interaction receivesCondition source inside).nodes)
    (different : node ≠ (boundary.interactionStopPath interaction receivesCondition source inside).endpoint) :
    interaction node = false := by
  let first := boundary.firstInteraction interaction receivesCondition source inside
  change node ∈ first.before ++ [first.target] at visited
  change node ≠ first.target at different
  rcases List.mem_append.mp visited with before | endpoint
  · exact first.before_free node before
  · exact False.elim (different (List.mem_singleton.mp endpoint))

/-- Union of the complete stopped traces from every original Small source.
Proof-bearing member entries certify the source mask; the returned data are
ordinary finite lists and Boolean membership scans. -/
def absorbingNodes : NodeSet S := fun node =>
  (NodeSet.members w.small).attach.any (fun source => decide
    (node ∈ (boundary.interactionStopPath interaction receivesCondition source.val
      ((NodeSet.mem_members_iff _ _).mp source.property)).nodes))

/-- A selected absorber row belongs to an actual stopped Small-source
trace.  This existential description is used only in propositional proofs. -/
theorem absorbingNodes_eq_true_iff (node : Fin S.count) :
    boundary.absorbingNodes interaction receivesCondition node = true ↔
      Exists fun source : Fin S.count => Exists fun inside : w.small source = true =>
        node ∈ (boundary.interactionStopPath interaction receivesCondition source inside).nodes := by
  unfold absorbingNodes
  rw [List.any_eq_true]
  constructor
  · rintro ⟨source, _member, visited⟩
    exact ⟨source.val, (NodeSet.mem_members_iff _ _).mp source.property, of_decide_eq_true visited⟩
  · rintro ⟨source, inside, visited⟩
    let entry : { source // source ∈ NodeSet.members w.small } :=
      ⟨source, (NodeSet.mem_members_iff _ _).mpr inside⟩
    exact ⟨entry, List.mem_attach _ _, decide_eq_true visited⟩

/-- Every mandatory Small row starts its own retained trace; no source
is omitted merely because another source has already reached the interaction. -/
theorem small_subset_absorbingNodes : NodeSet.Subset w.small (boundary.absorbingNodes interaction receivesCondition) := by
  intro source inside
  exact (boundary.absorbingNodes_eq_true_iff interaction receivesCondition source).mpr
    ⟨source, inside, List.mem_of_head? (boundary.interactionStopPath interaction receivesCondition source inside).starts⟩

/-- The pruned union remains inside the original action-free flow domain. -/
theorem absorbingNodes_subset_flow :
    NodeSet.Subset (boundary.absorbingNodes interaction receivesCondition) w.smallOutcomeFlowNodes := by
  intro node selected
  rcases (boundary.absorbingNodes_eq_true_iff interaction receivesCondition node).mp selected with ⟨source, inside, visited⟩
  exact (boundary.interactionStopPath interaction receivesCondition source inside).inside node visited

/-- Full original-action freedom is inherited by every added absorber row. -/
theorem absorbingNodes_action_free (node : Fin S.count)
    (selected : boundary.absorbingNodes interaction receivesCondition node = true) : query.action node = false :=
  outcomeFlow_avoids_action w node (boundary.absorbingNodes_subset_flow interaction receivesCondition node selected)

/-- The complete-trace union is closed under the one stopped successor.
Several Small-source branches may merge; closure does not require a tree. -/
theorem absorbingNodes_successor_closed (parent child : Fin S.count)
    (selected : boundary.absorbingNodes interaction receivesCondition parent = true)
    (edge : w.smallInteractionStopSuccessor interaction parent = some child) :
    boundary.absorbingNodes interaction receivesCondition child = true := by
  rcases (boundary.absorbingNodes_eq_true_iff interaction receivesCondition parent).mp selected with ⟨source, inside, visited⟩
  exact (boundary.absorbingNodes_eq_true_iff interaction receivesCondition child).mpr
    ⟨source, inside, (boundary.interactionStopPath interaction receivesCondition source inside).successor_mem parent child visited edge⟩

/-- Prune only the transmitting domain.  Every interaction contact keeps
`none`, including a contact shared by several mandatory-source traces. -/
def absorbingSuccessor : ForestChild S :=
  restrictChild (boundary.absorbingNodes interaction receivesCondition) (w.smallInteractionStopSuccessor interaction)

/-- Closure supplies the destination certificate needed for pruning.
Every retained arrow is still a declared arrow of the original signature. -/
theorem absorbingSuccessor_wellFormed :
    childWellFormedBool (boundary.absorbingNodes interaction receivesCondition)
      (boundary.absorbingSuccessor interaction receivesCondition) = true := by
  apply List.all_eq_true.mpr
  intro parent _member
  cases selected : boundary.absorbingNodes interaction receivesCondition parent with
  | false => simp only [absorbingSuccessor, restrictChild, selected, Bool.false_eq_true, if_false]
  | true =>
      cases next : w.smallInteractionStopSuccessor interaction parent with
      | none => simp only [absorbingSuccessor, restrictChild, selected, if_true, next]
      | some child =>
          have kept := boundary.absorbingNodes_successor_closed interaction receivesCondition parent child selected next
          have actual := (childWellFormed_edge w.smallOutcomeFlowNodes (w.smallInteractionStopSuccessor interaction)
            (w.smallInteractionStopSuccessor_wellFormed interaction) next).2.2
          simp only [absorbingSuccessor, restrictChild, selected, if_true, next, kept, actual, Bool.and_self]

/-- Every receiving row is stopped globally, whether or not it belongs
to a retained Small-source trace.  There is no fall-through at a zero-edge contact. -/
theorem absorbingSuccessor_stops (node : Fin S.count) (selected : interaction node = true) :
    boundary.absorbingSuccessor interaction receivesCondition node = none := by
  cases retained : boundary.absorbingNodes interaction receivesCondition node <;>
    simp only [absorbingSuccessor, restrictChild, retained, Bool.false_eq_true, if_false,
      if_true, HedgeWitness.smallInteractionStopSuccessor, selected]

/-- Every actual pruned sink is a receiving row.  A stopped visited node
is the endpoint of its complete trace, whose first-contact certificate gives
membership.  No all-sinks-inside flag is supplied by a terminal caller. -/
theorem absorbingSinks_subset_interaction :
    NodeSet.Subset (keptSinks (boundary.absorbingNodes interaction receivesCondition)
      (boundary.absorbingSuccessor interaction receivesCondition)) interaction := by
  intro node sink
  have parts := (keptSinks_iff _ _ node).mp sink
  rcases (boundary.absorbingNodes_eq_true_iff interaction receivesCondition node).mp parts.1 with ⟨source, inside, visited⟩
  have stopped : w.smallInteractionStopSuccessor interaction node = none := by
    have pruned := parts.2
    change restrictChild (boundary.absorbingNodes interaction receivesCondition)
      (w.smallInteractionStopSuccessor interaction) node = none at pruned
    exact (restrictChild_of_true parts.1).symm.trans pruned
  have same := (boundary.interactionStopPath interaction receivesCondition source inside).eq_endpoint_of_stopped node visited stopped
  rw [same]
  exact boundary.interactionStopPath_endpoint_in_interaction interaction receivesCondition source inside

/-- Within the actual pruned domain, sinks are precisely receiving rows.
This is an exact stopping contract, not just one-sided sink coverage. -/
theorem absorbingSuccessor_sink_iff_interaction (node : Fin S.count)
    (retained : boundary.absorbingNodes interaction receivesCondition node = true) :
    boundary.absorbingSuccessor interaction receivesCondition node = none ↔ interaction node = true := by
  constructor
  · intro stopped
    exact boundary.absorbingSinks_subset_interaction interaction receivesCondition node
      ((keptSinks_iff _ _ node).mpr ⟨retained, stopped⟩)
  · exact boundary.absorbingSuccessor_stops interaction receivesCondition node

-- Pruning keeps every vertex of a selected complete trace.  The helper
-- changes only edge certificates; it does not replace any path data.
private theorem consecutive_restrict (nodes : NodeSet S) (successor : ForestChild S) :
    forall route : List (Fin S.count),
      Consecutive (fun parent child => successor parent = some child) route ->
      (forall node, node ∈ route -> nodes node = true) ->
      Consecutive (fun parent child => restrictChild nodes successor parent = some child) route
  | [], _, _ => True.intro
  | [_], _, _ => True.intro
  | parent :: child :: rest, directed, inside =>
      ⟨(restrictChild_of_true (inside parent (List.mem_cons.mpr (Or.inl rfl)))).trans directed.1,
        consecutive_restrict nodes successor (child :: rest) directed.2
          (fun node member => inside node (List.mem_cons.mpr (Or.inr member)))⟩

/-- Repackage the exact first-contact list in the installed pruned domain.
No selected edge, shared suffix or zero-edge source contact is lost. -/
def absorbingPath (source : Fin S.count) (inside : w.small source = true) :
    SuccessorPath (boundary.absorbingNodes interaction receivesCondition)
      (boundary.absorbingSuccessor interaction receivesCondition) source := by
  let original := boundary.interactionStopPath interaction receivesCondition source inside
  have retained : forall node, node ∈ original.nodes -> boundary.absorbingNodes interaction receivesCondition node = true := by
    intro node visited
    exact (boundary.absorbingNodes_eq_true_iff interaction receivesCondition node).mpr ⟨source, inside, visited⟩
  refine {
    nodes := original.nodes
    endpoint := original.endpoint
    starts := original.starts
    finishes := original.finishes
    simple := original.simple
    consecutive := consecutive_restrict _ _ original.nodes original.consecutive retained
    stopped := ?_
    inside := retained
  }
  change restrictChild (boundary.absorbingNodes interaction receivesCondition)
    (w.smallInteractionStopSuccessor interaction) original.endpoint = none
  rw [restrictChild_of_true (retained original.endpoint (List.mem_of_getLast? original.finishes))]
  exact original.stopped

/-- The installed complete trace is the literal original first-contact
prefix, not an extension chosen after changing the transmitting domain. -/
theorem absorbingPath_nodes (source : Fin S.count) (inside : w.small source = true) :
    (boundary.absorbingPath interaction receivesCondition source inside).nodes =
      (boundary.interactionStopPath interaction receivesCondition source inside).nodes := rfl

/-- Pruning retains the actual receiving endpoint along with the list. -/
theorem absorbingPath_endpoint (source : Fin S.count) (inside : w.small source = true) :
    (boundary.absorbingPath interaction receivesCondition source inside).endpoint =
      (boundary.interactionStopPath interaction receivesCondition source inside).endpoint := rfl

end ConditionedSmallFlowBoundary

/-! ## Complete normalized interactions now have actual full-Small absorption -/

namespace ConditionalBackdoorPathNormalForm

variable {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    {w : HedgeWitness graph query.jointNumerator}
    (boundary : ConditionedSmallFlowBoundary w) (pivot : RetainedConditionalPivot query)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalCutColliderActivationForest query pivot.node)

/-- The actual union retaining every original Small row and every completed
normalized-interaction row.  First contacts may overlap Small or each other. -/
def smallAbsorbedInteractionRows : NodeSet S :=
  NodeSet.union (normal.smallInteractionRows pivot forest)
    (boundary.absorbingNodes (normal.smallInteractionRows pivot forest) (NodeSet.subset_union_right _ _))

/-- Add the certified Small-forest inputs to the existing legal signal,
retaining a receiving mechanism's own bit once rather than XORing whole rows. -/
def smallAbsorbedInteractionSignal : LinearSignal graph :=
  (normal.activationInteractionSignal pivot forest).absorbSuccessor (normal.smallInteractionRows pivot forest)
    (boundary.absorbingSuccessor (normal.smallInteractionRows pivot forest) (NodeSet.subset_union_right _ _))

/-- The actual background is precisely the installed union outside the
whole original Small set.  Overlap is retained once at its mandatory row. -/
def smallAbsorbedInteractionBackgroundRows : NodeSet S :=
  NodeSet.diff (normal.smallAbsorbedInteractionRows boundary pivot forest) w.small

/-- Complete mandatory Small coverage is now derived from the actual
boundary paths.  It is not an additional normalized-countermodel premise. -/
theorem smallAbsorbedInteraction_contains_small : NodeSet.Subset w.small (normal.smallAbsorbedInteractionRows boundary pivot forest) := by
  intro node inside
  exact NodeSet.subset_union_right _ _ node
    (boundary.small_subset_absorbingNodes (normal.smallInteractionRows pivot forest) (NodeSet.subset_union_right _ _) node inside)

/-- Original interaction rows and all newly routed rows avoid the complete
original action set, so neither source of the union installs an acted-on row. -/
theorem smallAbsorbedInteraction_action_free (node : Fin S.count)
    (selected : normal.smallAbsorbedInteractionRows boundary pivot forest node = true) : query.action node = false := by
  rcases Bool.or_eq_true_iff.mp selected with original | absorbed
  · exact normal.smallInteractionRows_action_free pivot forest node original
  · exact boundary.absorbingNodes_action_free (normal.smallInteractionRows pivot forest) (NodeSet.subset_union_right _ _) node absorbed

/-- Whole-cube conservation at all first contacts and branch merges.
No direction, zero-tail assumption or matched evidence denominator is needed:
this identity holds for every assignment of observed and original reserved bits. -/
theorem smallAbsorbedInteraction_phase (point : Cube graph) :
    ((normal.smallAbsorbedInteractionSignal boundary pivot forest).forestPhase
      (normal.smallAbsorbedInteractionRows boundary pivot forest)).value point =
      ((normal.activationInteractionSignal pivot forest).forestPhase (normal.smallInteractionRows pivot forest)).value point :=
  LinearSignal.absorbSuccessor_forestPhase _ _ _ _
    (boundary.absorbingSuccessor_wellFormed (normal.smallInteractionRows pivot forest) (NodeSet.subset_union_right _ _))
    (boundary.absorbingSuccessor_stops (normal.smallInteractionRows pivot forest) (NodeSet.subset_union_right _ _))
    (boundary.absorbingSinks_subset_interaction (normal.smallInteractionRows pivot forest) (NodeSet.subset_union_right _ _)) point

/-- Absorption preserves the original outcome character on the full
original evidence cylinder, not only at one supported balance direction.
The direction's row-wise parity conditions still require a separate proof. -/
theorem smallAbsorbedInteraction_conditionalPhase (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    ((normal.smallAbsorbedInteractionSignal boundary pivot forest).forestPhase
      (normal.smallAbsorbedInteractionRows boundary pivot forest)).value point =
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point := by
  rw [normal.smallAbsorbedInteraction_phase boundary pivot forest point]
  exact normal.smallInteraction_conditionalPhase pivot forest point listed

/-- Every background row is outside the full original Small set, not
merely outside one source approach or one normalized path fragment. -/
theorem smallAbsorbedInteractionBackground_outside_small (node : Fin S.count)
    (selected : normal.smallAbsorbedInteractionBackgroundRows boundary pivot forest node = true) : w.small node = false := by
  simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp selected).2

/-- The actual outside-Small background also avoids the original action. -/
theorem smallAbsorbedInteractionBackground_action_free (node : Fin S.count)
    (selected : normal.smallAbsorbedInteractionBackgroundRows boundary pivot forest node = true) : query.action node = false :=
  normal.smallAbsorbedInteraction_action_free boundary pivot forest node (Bool.and_eq_true_iff.mp selected).1

/-- The complete mandatory Small phase and the deduplicated background
have the exact covariance matching identity throughout the original evidence
cylinder.  Full Small coverage and conservation prove the identity; no
matched-denominator or direction-parity certificate is supplied.  To obtain a
countermodel one still needs a supported direction making the outcome odd and
every one of these actual background rows even. -/
theorem smallAbsorbedInteraction_matching (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    (((normal.smallAbsorbedInteractionSignal boundary pivot forest).forestPhase w.small).xor
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome)))).value point =
      (selectedPhase _ S.count (normal.smallAbsorbedInteractionBackgroundRows boundary pivot forest)
        (normal.smallAbsorbedInteractionSignal boundary pivot forest).rowPhase).value point := by
  let data := normal.smallAbsorbedInteractionSignal boundary pivot forest
  let background := normal.smallAbsorbedInteractionBackgroundRows boundary pivot forest
  have partition : NodeSet.union w.small background = normal.smallAbsorbedInteractionRows boundary pivot forest :=
    NodeSet.union_diff_eq (normal.smallAbsorbedInteraction_contains_small boundary pivot forest)
  have whole : Bool.xor ((data.forestPhase w.small).value point)
      ((selectedPhase _ S.count background data.rowPhase).value point) =
      (maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point := by
    rw [LinearSignal.selectedPhase_value_eq_forestPhase,
      ← LinearSignal.forestPhase_union_of_disjoint data w.small background
        (NodeSet.disjoint_diff (normal.smallAbsorbedInteractionRows boundary pivot forest) w.small),
      partition]
    exact normal.smallAbsorbedInteraction_conditionalPhase boundary pivot forest point listed
  change Bool.xor ((data.forestPhase w.small).value point)
    ((maskPhase _ (cubeMask graph (NodeSet.singleton normal.outcome))).value point) = _
  rw [← whole]
  generalize (data.forestPhase w.small).value point = smallBit
  generalize (selectedPhase _ S.count background data.rowPhase).value point = backgroundBit
  cases smallBit <;> cases backgroundBit <;> rfl

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
