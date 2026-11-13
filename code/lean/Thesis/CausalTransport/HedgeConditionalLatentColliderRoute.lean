import Thesis.CausalTransport.HedgeConditionalLatentCollider
import Thesis.CausalTransport.ConditionalLatentColliderNonInfluence
import Thesis.CausalTransport.HedgeConditionalColliderRoute

namespace Thesis
namespace Causality

open Probability

/-!
# Shared-latent collider entry followed by arbitrary directed readouts

A conditioned common root may have an outside shared-latent neighbour which
is not itself queried.  Its actual collider countermodel can instead be read
along a finite directed route to an original queried outcome.  The whole
original action and full common-root conditioner are retained throughout.

The original hedge supplies the separated root and supported context.  Its
auxiliary singleton-source numerator still contains every common root, so
reindexing preserves the forests, action seed, carrier pair and source gap.
The shared-latent constructor then installs its own source countermodels.
Their route readiness is proved from the actual mechanisms, not supplied as
an assumed invariant or inferred from the topological order of the collider.

The finite graph wrapper searches an outside, unacted neighbour incident to
an existing bidirected edge, then an original outcome reachable while cutting
the action and large forest.  The shared directed-tail certificate supplies
all destination conditions.  No observed arrow from that neighbour into the
conditioned root is required or introduced, and the neighbour need not be in
the original queried outcome.

There is no bound on the number of directed tail arrows or common roots.
This still covers a particular active-path family: the conditioner equals
the common roots and the directed tail avoids the large forest.  General
internal responding routes and collider-rich paths remain distinct semantic
obligations of the universal conditional completeness theorem.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S}
  {query : ConditionalKernelQuery S}

namespace HedgeConditionalRoot.Witness

/-- Construct the whole original-query countermodel from a shared-latent
entry and a directed readout tail.  Both the source pair and its non-influence
are derived internally.  The entry noise and each destination's private
noise may have different supported nonzero biases. -/
noncomputable def positiveConditionalCounterexampleAlongSharedLatentRouteWithNoise
    {w : HedgeWitness graph query.jointNumerator} {rich : ObservedSignature.ValueRich S}
    (selected : HedgeConditionalRoot.Witness w rich)
    (roots : w.roots = query.condition) (parent endpoint : Fin S.count)
    (outside : w.large parent = false) (parentUnacted : query.action parent = false)
    (edge : graph.bidirected parent selected.root = true)
    (route : ConditionalReadout.Route S parent endpoint)
    (endpointSelected : query.outcome endpoint = true)
    (unacted : forall node, node ∈ route.destinations -> query.action node = false)
    (ungiven : forall node, node ∈ route.destinations -> query.condition node = false)
    (sinks : forall node, node ∈ route.destinations -> w.child node = none)
    (colliderNoise : FiniteProbRecord Bool)
    (colliderPositive : forall bit, colliderNoise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (colliderGap : Nat) (colliderGapPositive : 0 < colliderGap)
    (colliderBias : FiniteProbRecord.eventMass colliderNoise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass colliderNoise.atoms id + colliderGap)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (noisePositive : forall node, node ∈ route.destinations ->
      forall bit, (noise node).EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : (node : Fin S.count) -> Nat)
    (positiveGap : forall node, node ∈ route.destinations -> 0 < gap node)
    (bias : forall node, node ∈ route.destinations ->
      FiniteProbRecord.eventMass (noise node).atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass (noise node).atoms id + gap node) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  have parentUngiven : query.condition parent = false :=
    (congrFun roots parent).symm.trans (w.roots_false_of_large_false parent outside)
  let source := ConditionalReadout.singletonQuery query parent parentUnacted parentUngiven
  have containsRoots : NodeSet.Subset w.roots source.jointNumerator.outcome := by
    intro node root
    exact Bool.or_eq_true_iff.mpr (Or.inr ((congrFun roots node).symm.trans root))
  let sourceHedge := w.withOutcomeContainingRoots source.jointNumerator rfl containsRoots
    selected.root selected.root_selected
  -- Preserve the actual separated root, original action values and full-label
  -- reference.  Changing only the outcome index does not change either carrier
  -- SCM, and no propositional existence statement is eliminated into data.
  let sourceSelected : HedgeConditionalRoot.Witness sourceHedge rich := {
    root := selected.root
    root_selected := selected.root_selected
    reference := selected.reference
    action_values := selected.action_values
    left_supported := selected.left_supported
    right_supported := selected.right_supported
    separated := selected.separated
  }
  let seed := sourceSelected.positiveConditionalCounterexampleWithSharedLatentNoise parent
    ((NodeSet.singleton_eq_true_iff parent parent).mpr rfl) roots outside edge
    colliderNoise colliderPositive colliderGap colliderGapPositive colliderBias
  -- The shared mask is latent and the private child replacement preserves
  -- every initially ignored observed coordinate.  No destination/collider
  -- order hypothesis or undeclared observed arrow is smuggled into readiness.
  have leftIgnored (node : Fin S.count) (listed : node ∈ route.destinations) :
      seed.left.OtherMechanismsIgnore node :=
    ConditionalLatentCollider.model_otherMechanismsIgnore _ sourceSelected.readoutValues
      parent sourceSelected.root colliderNoise node
      (w.largeCarrierDefectParityModel_otherMechanismsIgnore rich node (sinks node listed))
  have rightIgnored (node : Fin S.count) (listed : node ∈ route.destinations) :
      seed.right.OtherMechanismsIgnore node :=
    ConditionalLatentCollider.model_otherMechanismsIgnore _ sourceSelected.readoutValues
      parent sourceSelected.root colliderNoise node
      (w.smallCarrierDefectParityModel_otherMechanismsIgnore rich node (sinks node listed))
  exact ConditionalReadout.ofRouteWithNoise source query seed rich route rfl endpointSelected rfl rfl
    unacted ungiven leftIgnored rightIgnored noise noisePositive gap positiveGap bias

/-- Explicit supported `2:1` stay/flip noise at the shared-latent entry and
every directed readout.  The original geometry is unchanged; no epsilon,
source countermodel or separated cell is chosen from an existence claim. -/
noncomputable def positiveConditionalCounterexampleAlongSharedLatentRoute
    {w : HedgeWitness graph query.jointNumerator} {rich : ObservedSignature.ValueRich S}
    (selected : HedgeConditionalRoot.Witness w rich)
    (roots : w.roots = query.condition) (parent endpoint : Fin S.count)
    (outside : w.large parent = false) (parentUnacted : query.action parent = false)
    (edge : graph.bidirected parent selected.root = true)
    (route : ConditionalReadout.Route S parent endpoint)
    (endpointSelected : query.outcome endpoint = true)
    (unacted : forall node, node ∈ route.destinations -> query.action node = false)
    (ungiven : forall node, node ∈ route.destinations -> query.condition node = false)
    (sinks : forall node, node ∈ route.destinations -> w.child node = none) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  selected.positiveConditionalCounterexampleAlongSharedLatentRouteWithNoise roots parent endpoint outside
    parentUnacted edge route endpointSelected unacted ungiven sinks
    (FiniteProbRecord.biasedFlip 1 1 (by decide)) (by intro bit; cases bit <;> decide +kernel)
    1 (by decide) (by decide +kernel) (fun _ => FiniteProbRecord.biasedFlip 1 1 (by decide))
    (by intro node listed bit; dsimp only; cases bit <;> decide +kernel)
    (fun _ => 1) (by intro node listed; change 0 < 1; decide)
    (by intro node listed; dsimp only; decide +kernel)

end HedgeConditionalRoot.Witness

namespace HedgeConditionalRoot

/-! ## Constructive shared-latent entry and directed-tail selection -/

/-- The graph data for one root's latent entry and directed tail.  `parent`
is its channel role, not an assertion of an observed arrow into the root.
The original outcome occurs at the endpoint, which may differ from parent. -/
structure SharedLatentIncomingRoute (w : HedgeWitness graph query.jointNumerator) (root : Fin S.count) where
  parent : Fin S.count
  endpoint : Fin S.count
  outside : w.large parent = false
  parent_unacted : query.action parent = false
  edge : graph.bidirected parent root = true
  route : ConditionalReadout.Route S parent endpoint
  endpoint_selected : query.outcome endpoint = true
  destinations_unacted : forall node, node ∈ route.destinations -> query.action node = false
  destinations_ungiven : forall node, node ∈ route.destinations -> query.condition node = false
  destinations_sinks : forall node, node ∈ route.destinations -> w.child node = none

/-- Search all observed vertices for an outside, unacted shared neighbour
which has an admissible directed tail to an original outcome.  The old
queried-neighbour family is the zero-length-tail boundary of this test. -/
def sharedLatentRouteParentMask (w : HedgeWitness graph query.jointNumerator)
    (root : Fin S.count) : NodeSet S :=
  fun parent => (!w.large parent && !query.action parent) &&
    (graph.bidirected parent root && NodeSet.meetsBool query.outcome (incomingRouteEndpointMask w parent))

/-- Return the actual finite-search entry and tail.  The same incoming-cut
tail proof is shared with observed entries, while the first incidence is
retained as a bidirected edge rather than converted to an observed arrow. -/
def sharedLatentIncomingRoute (w : HedgeWitness graph query.jointNumerator)
    (roots : w.roots = query.condition) (root : Fin S.count)
    (available : NodeSet.meetsBool NodeSet.full (sharedLatentRouteParentMask w root) = true) :
    SharedLatentIncomingRoute w root := by
  let parent := NodeSet.getMeeting NodeSet.full (sharedLatentRouteParentMask w root) available
  have passed := Bool.and_eq_true_iff.mp (NodeSet.getMeeting_right available)
  have parentParts := Bool.and_eq_true_iff.mp passed.1
  have routeParts := Bool.and_eq_true_iff.mp passed.2
  have outside : w.large parent = false := by
    cases included : w.large parent with
    | false => rfl
    | true =>
        have impossible := parentParts.1
        rw [included] at impossible
        cases impossible
  have parentUnacted : query.action parent = false := by
    cases acted : query.action parent with
    | false => rfl
    | true =>
        have impossible := parentParts.2
        rw [acted] at impossible
        cases impossible
  let tail := outsideRoute w roots parent routeParts.2
  exact {
    parent := parent
    endpoint := tail.endpoint
    outside := outside
    parent_unacted := parentUnacted
    edge := routeParts.1
    route := tail.route
    endpoint_selected := tail.endpoint_selected
    destinations_unacted := tail.destinations_unacted
    destinations_ungiven := tail.destinations_ungiven
    destinations_sinks := tail.destinations_sinks
  }

end HedgeConditionalRoot

/-- Select the actual separated root, its own shared-latent neighbour, and
its complete directed tail from finite graph tests.  Different roots may
have different neighbours, original endpoints and tail lengths. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootSpecificLatentRoutesWithNoise
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (roots : w.roots = query.condition)
    (routesAvailable : forall root, w.roots root = true ->
      NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.sharedLatentRouteParentMask w root) = true)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  let selected := w.conditionedRoot rich
  let geometry := HedgeConditionalRoot.sharedLatentIncomingRoute w roots selected.root
    (routesAvailable selected.root selected.root_selected)
  selected.positiveConditionalCounterexampleAlongSharedLatentRouteWithNoise roots geometry.parent geometry.endpoint
    geometry.outside geometry.parent_unacted geometry.edge geometry.route geometry.endpoint_selected
    geometry.destinations_unacted geometry.destinations_ungiven geometry.destinations_sinks
    noise noisePositive gap positiveGap bias (fun _ => noise) (fun _ _ => noisePositive)
    (fun _ => gap) (fun _ _ => positiveGap) (fun _ _ => bias)

/-- Supported `2:1` noise with all source and route data constructed by the
hedge-root selector and finite graph searches.  This is an actual whole-query
positive countermodel, not a promise to supply its semantic fields later. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootSpecificLatentRoutes
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (roots : w.roots = query.condition)
    (routesAvailable : forall root, w.roots root = true ->
      NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.sharedLatentRouteParentMask w root) = true) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  w.positiveConditionalCounterexampleOfRootSpecificLatentRoutesWithNoise rich roots routesAvailable
    (FiniteProbRecord.biasedFlip 1 1 (by decide)) (by intro bit; cases bit <;> decide +kernel)
    1 (by decide) (by decide +kernel)

end Causality
end Thesis
