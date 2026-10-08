import Thesis.CausalTransport.HedgeConditionalCollider
import Thesis.CausalTransport.ConditionalColliderNonInfluence
import Thesis.CausalTransport.ConditionalReadoutRoute
import Thesis.CausalTransport.ConditionalReadoutReachability
import Thesis.Causality.HedgeQuery

namespace Thesis
namespace Causality

open Probability

/-!
# Positive hedge countermodels through a collider and a finite directed route

The selected separated common root need not have an incoming parent already
in the original queried outcome.  An outside, unacted parent can carry the
collider's conditional gap along a finite directed route to that outcome.
This module constructs the auxiliary singleton query, its reindexed hedge,
the actual collider countermodel, and the readiness of both seed SCMs.

The root selection and source gap belong to the original positive carrier
pair.  Reindexing the hedge changes neither forest, the action seed, nor the
actual pair.  The whole common-root set remains the conditioner, including
its full observed labels.  The generic route adapter then installs its own
private readouts, deriving a fresh separated cell at each step rather than
assuming a gap of an already modified kernel.

Only graph geometry is supplied: a declared edge from the outside parent to
the selected root, a route to an original outcome, and free, ungiven route
destinations with no kept forest child.  Initial and intermediate semantic
non-influence proofs are constructed internally.  The collider need not
precede those destinations in the ambient topological order, and ambient
edges into the collider may be ignored by its actual mechanism.

There is no bound on the number of roots or route arrows, and additional
original outcomes are retained.  This closes this directed-fork family;
mixed active paths, internal responding forest destinations, and a general
terminal countermodel are still distinct obligations.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S}
  {query : ConditionalKernelQuery S}

namespace HedgeConditionalRoot.Witness

/-- An outside parent cannot be one of the conditioned common roots.  This
uses the actual large forest, not an extra semantic non-influence premise. -/
private theorem parent_ungiven {w : HedgeWitness graph query.jointNumerator}
    (roots : w.roots = query.condition) (parent : Fin S.count)
    (outside : w.large parent = false) : query.condition parent = false := by
  cases given : query.condition parent with
  | false => rfl
  | true =>
      have root : w.roots parent = true := (congrFun roots parent).trans given
      have inside := ((w.large_forest.roots_exact parent).mp root).1
      rw [outside] at inside
      cases inside

/-- Carry an actual separated-root hedge witness to the whole original
query through an auxiliary collider parent and an arbitrary directed route.
The seed models and every route readiness proof are derived from the hedge.
The collider and different route destinations may use independent noise
records with different supported nonzero biases. -/
noncomputable def positiveConditionalCounterexampleAlongRouteWithNoise
    {w : HedgeWitness graph query.jointNumerator} {rich : ObservedSignature.ValueRich S}
    (selected : HedgeConditionalRoot.Witness w rich)
    (roots : w.roots = query.condition) (parent endpoint : Fin S.count)
    (outside : w.large parent = false) (parentUnacted : query.action parent = false)
    (edge : S.directed parent selected.root = true)
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
  let source := ConditionalReadout.singletonQuery query parent parentUnacted (parent_ungiven roots parent outside)
  have containsRoots : NodeSet.Subset w.roots source.jointNumerator.outcome := by
    intro node root
    exact Bool.or_eq_true_iff.mpr (Or.inr ((congrFun roots node).symm.trans root))
  let sourceHedge := w.withOutcomeContainingRoots source.jointNumerator rfl containsRoots
    selected.root selected.root_selected
  -- The forest, action seed, defect root and carrier pair are unchanged.
  -- The existing separated cell is copied as actual data; it is not selected
  -- again from a proposition, and its conditioner and intervention are kept.
  let sourceSelected : HedgeConditionalRoot.Witness sourceHedge rich := {
    root := selected.root
    root_selected := selected.root_selected
    reference := selected.reference
    action_values := selected.action_values
    left_supported := selected.left_supported
    right_supported := selected.right_supported
    separated := selected.separated
  }
  let seed := sourceSelected.positiveConditionalCounterexampleWithNoise parent
    ((NodeSet.singleton_eq_true_iff parent parent).mpr rfl) roots outside edge
    colliderNoise colliderPositive colliderGap colliderGapPositive colliderBias
  have different (node : Fin S.count) (listed : node ∈ route.destinations) : parent ≠ node := by
    intro same
    have earlier := route.source_lt_destination node listed
    rw [same] at earlier
    exact Nat.lt_irrefl _ earlier
  have leftIgnored (node : Fin S.count) (listed : node ∈ route.destinations) :
      seed.left.OtherMechanismsIgnore node :=
    ConditionalCollider.model_otherMechanismsIgnore _ sourceSelected.readoutValues parent
      sourceSelected.root edge colliderNoise node (different node listed)
      (w.largeCarrierDefectParityModel_otherMechanismsIgnore rich node (sinks node listed))
  have rightIgnored (node : Fin S.count) (listed : node ∈ route.destinations) :
      seed.right.OtherMechanismsIgnore node :=
    ConditionalCollider.model_otherMechanismsIgnore _ sourceSelected.readoutValues parent
      sourceSelected.root edge colliderNoise node (different node listed)
      (w.smallCarrierDefectParityModel_otherMechanismsIgnore rich node (sinks node listed))
  exact ConditionalReadout.ofRouteWithNoise source query seed rich route rfl endpointSelected rfl rfl
    unacted ungiven leftIgnored rightIgnored noise noisePositive gap positiveGap bias

/-- The same whole-query collider/route construction with explicit supported
`2:1` stay/flip noise throughout.  Geometry is unchanged; no positive epsilon,
source kernel gap, seed countermodel or intermediate SCM invariant is chosen. -/
noncomputable def positiveConditionalCounterexampleAlongRoute
    {w : HedgeWitness graph query.jointNumerator} {rich : ObservedSignature.ValueRich S}
    (selected : HedgeConditionalRoot.Witness w rich)
    (roots : w.roots = query.condition) (parent endpoint : Fin S.count)
    (outside : w.large parent = false) (parentUnacted : query.action parent = false)
    (edge : S.directed parent selected.root = true)
    (route : ConditionalReadout.Route S parent endpoint)
    (endpointSelected : query.outcome endpoint = true)
    (unacted : forall node, node ∈ route.destinations -> query.action node = false)
    (ungiven : forall node, node ∈ route.destinations -> query.condition node = false)
    (sinks : forall node, node ∈ route.destinations -> w.child node = none) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  selected.positiveConditionalCounterexampleAlongRouteWithNoise roots parent endpoint outside parentUnacted
    edge route endpointSelected unacted ungiven sinks
    (FiniteProbRecord.biasedFlip 1 1 (by decide)) (by intro bit; cases bit <;> decide +kernel)
    1 (by decide) (by decide +kernel) (fun _ => FiniteProbRecord.biasedFlip 1 1 (by decide))
    (by intro node listed bit; dsimp only; cases bit <;> decide +kernel)
    (fun _ => 1) (by intro node listed; change 0 < 1; decide)
    (by intro node listed; dsimp only; decide +kernel)

end HedgeConditionalRoot.Witness

namespace HedgeConditionalRoot

/-! ## Finite graph selection of an auxiliary parent and its route -/

/-- Graph certificate for one root's incoming parent and its directed
readout route.  The source need not be queried; the final vertex is queried.
The displayed destination conditions are checked before any SCM is built. -/
structure IncomingRoute (w : HedgeWitness graph query.jointNumerator) (root : Fin S.count) where
  parent : Fin S.count
  endpoint : Fin S.count
  outside : w.large parent = false
  parent_unacted : query.action parent = false
  edge : S.directed parent root = true
  route : ConditionalReadout.Route S parent endpoint
  endpoint_selected : query.outcome endpoint = true
  destinations_unacted : forall node, node ∈ route.destinations -> query.action node = false
  destinations_ungiven : forall node, node ∈ route.destinations -> query.condition node = false
  destinations_sinks : forall node, node ∈ route.destinations -> w.child node = none

/-- A possible final outcome reached without entering either the large
forest or the original action.  Reachability is the existing finite Boolean
computation on the observed graph; no latent-path search is performed. -/
def incomingRouteEndpointMask (w : HedgeWitness graph query.jointNumerator)
    (parent : Fin S.count) : NodeSet S :=
  fun endpoint => FiniteReachability.within finBeq (NodeSet.enumerated S)
    (mutilatedDirected S (NodeSet.union query.action w.large)) S.count parent endpoint

/-- Root-local auxiliary-parent eligibility.  Parents are searched over the
whole signature, rather than only the original queried outcome.  The final
meeting test retains membership in the actual original outcome. -/
def incomingRouteParentMask (w : HedgeWitness graph query.jointNumerator)
    (root : Fin S.count) : NodeSet S :=
  fun parent => (!w.large parent && !query.action parent) &&
    (S.directed parent root && NodeSet.meetsBool query.outcome (incomingRouteEndpointMask w parent))

/-- Select both endpoints and build the intervening route from finite graph
tests.  Avoiding the incoming cut gives outside-forest and action avoidance;
root/condition equality gives conditioner avoidance, and the kept child of
an outside vertex is `none`.  No semantic readiness is supplied by the caller. -/
def incomingRoute (w : HedgeWitness graph query.jointNumerator)
    (roots : w.roots = query.condition) (root : Fin S.count)
    (available : NodeSet.meetsBool NodeSet.full (incomingRouteParentMask w root) = true) :
    IncomingRoute w root := by
  let parent := NodeSet.getMeeting NodeSet.full (incomingRouteParentMask w root) available
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
  let endpoint := NodeSet.getMeeting query.outcome (incomingRouteEndpointMask w parent) routeParts.2
  let certificate := ConditionalReadout.CutRoute.ofReachability
    (NodeSet.union query.action w.large) endpoint S.count parent (NodeSet.getMeeting_right routeParts.2)
  have free (node : Fin S.count) (listed : node ∈ certificate.route.destinations) :
      query.action node = false ∧ w.large node = false :=
    Bool.or_eq_false_iff.mp (certificate.destinations_free node listed)
  exact {
    parent := parent
    endpoint := endpoint
    outside := outside
    parent_unacted := parentUnacted
    edge := routeParts.1
    route := certificate.route
    endpoint_selected := NodeSet.getMeeting_left routeParts.2
    destinations_unacted := fun node listed => (free node listed).1
    destinations_ungiven := fun node listed => Witness.parent_ungiven roots node (free node listed).2
    destinations_sinks := fun node listed => w.large_forest.child_off_set node (free node listed).2
  }

end HedgeConditionalRoot

/-- Select the actual separated root first, then search its own auxiliary
parent, original outcome and complete directed route.  Different roots may
have different parents and paths.  The universal premise is a finite graph
availability test, not a source gap or an assumed countermodel family. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootSpecificColliderRoutesWithNoise
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (roots : w.roots = query.condition)
    (routesAvailable : forall root, w.roots root = true ->
      NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.incomingRouteParentMask w root) = true)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  let selected := w.conditionedRoot rich
  let geometry := HedgeConditionalRoot.incomingRoute w roots selected.root
    (routesAvailable selected.root selected.root_selected)
  selected.positiveConditionalCounterexampleAlongRouteWithNoise roots geometry.parent geometry.endpoint
    geometry.outside geometry.parent_unacted geometry.edge geometry.route geometry.endpoint_selected
    geometry.destinations_unacted geometry.destinations_ungiven geometry.destinations_sinks
    noise noisePositive gap positiveGap bias (fun _ => noise) (fun _ _ => noisePositive)
    (fun _ => gap) (fun _ _ => positiveGap) (fun _ _ => bias)

/-- Root-specific collider/route countermodels with explicit supported `2:1`
stay/flip noise.  All source and route data come from the constructive root
and graph searches; this wrapper introduces neither choice nor an epsilon. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootSpecificColliderRoutes
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (roots : w.roots = query.condition)
    (routesAvailable : forall root, w.roots root = true ->
      NodeSet.meetsBool NodeSet.full (HedgeConditionalRoot.incomingRouteParentMask w root) = true) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  w.positiveConditionalCounterexampleOfRootSpecificColliderRoutesWithNoise rich roots routesAvailable
    (FiniteProbRecord.biasedFlip 1 1 (by decide)) (by intro bit; cases bit <;> decide +kernel)
    1 (by decide) (by decide +kernel)

end Causality
end Thesis
