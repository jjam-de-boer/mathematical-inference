import Thesis.CausalTransport.HedgeConditionalCompensatedReadout

namespace Thesis
namespace Causality

open Probability

/-!
# Absorbing outer route vertices before constructing a hedge countermodel

The compensated carrier proof excludes updates at `large \ small`.
That exclusion cannot be dropped by treating the two original parent
responses as identical: only the nested model omits those parents at its
small rows.  This module changes the *forest witness first*, rather than
asserting observational equality of an unsupported update to the old pair.

The large forest, kept child map, common roots, original query, and stored
coordinates are retained.  The small forest may grow inside the large side
if it remains bidirected connected, avoids the action, and is closed under
kept children.  Common roots remain exactly the same.  Canonical outcome
routes therefore do not change, and routes absorbed into the new small set
can use the existing positive compensated countermodel construction.

The automatic candidate is the kept-descendant closure of the old small
set together with every large vertex on a canonical outcome route.  Closure
and large-side containment are proved, not supplied.  Only its finite
connectivity and action-avoidance tests remain.  Arbitrary larger connected
closed candidates are also permitted by the general constructor, for
example when extra non-route vertices supply a bidirected connection.

This is a real extension to outer-route cases, not the unrestricted hedge
theorem: an absorption candidate can meet the action or fail connectivity.
Neither failure is interpreted as proof that every other possible witness
or countermodel construction fails.
-/

/-! ## Growing the small forest without changing the original query -/

section Forests

variable {S : ObservedSignature}

/-- Enlarge the small side using only explicit structural data.  Existing
small vertices, and hence every common root, are retained.  Child closure
prevents an added row from keeping a successor outside the new forest.
No countermodel, probability equality, or changed query is assumed. -/
def HedgeWitness.enlargeSmall {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (nodes : NodeSet S)
    (containsSmall : NodeSet.Subset w.small nodes)
    (withinLarge : NodeSet.Subset nodes w.large)
    (connected : BidirectedComponent G nodes)
    (childClosed : forall parent child, nodes parent = true -> w.child parent = some child -> nodes child = true)
    (avoids : NodeSet.Disjoint nodes q.action) : HedgeWitness G q where
  large := w.large
  small := nodes
  roots := w.roots
  child := w.child
  large_forest := w.large_forest
  small_forest := {
    component := connected
    child_off_set := by
      intro parent absent
      simp only [restrictChild, absent, Bool.false_eq_true, if_false]
    child_edge := by
      intro parent child found
      cases selected : nodes parent with
      | false => simp only [restrictChild, selected, Bool.false_eq_true, if_false] at found; cases found
      | true =>
          have original : w.child parent = some child := by simpa only [restrictChild, selected, if_true] using found
          exact ⟨rfl, childClosed parent child selected original, (w.large_forest.child_edge parent child original).2.2⟩
    roots_exact := by
      intro node
      constructor
      · intro root
        have old := (w.small_forest.roots_exact node).mp root
        have selected := containsSmall node old.1
        have original := ((w.large_forest.roots_exact node).mp root).2
        exact ⟨selected, by simp only [restrictChild, selected, if_true, original]⟩
      · intro parts
        have original : w.child node = none := (restrictChild_of_true parts.1).symm.trans parts.2
        exact (w.large_forest.roots_exact node).mpr ⟨withinLarge node parts.1, original⟩ }
  small_subset_large := withinLarge
  large_meets_intervention := w.large_meets_intervention
  small_avoids_intervention := avoids
  roots_reach_outcome := w.roots_reach_outcome
  actionSeed := w.actionSeed
  actionSeed_in_large := w.actionSeed_in_large
  actionSeed_in_action := w.actionSeed_in_action
  outcomeSeed := w.outcomeSeed
  outcomeSeed_in_outcome := w.outcomeSeed_in_outcome

/-- Canonical routes depend on the common roots and original query, not
the choice of the small forest.  Their preservation is definitional; no
finite route is reselected from a propositional reachability witness. -/
theorem HedgeWitness.enlargeSmall_rootReadoutNodes
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (nodes : NodeSet S) (containsSmall : NodeSet.Subset w.small nodes) (withinLarge : NodeSet.Subset nodes w.large)
    (connected : BidirectedComponent G nodes)
    (childClosed : forall parent child, nodes parent = true -> w.child parent = some child -> nodes child = true)
    (avoids : NodeSet.Disjoint nodes q.action) :
    (w.enlargeSmall nodes containsSmall withinLarge connected childClosed avoids).rootReadoutNodes = w.rootReadoutNodes := rfl

/-! ## The least kept-child-closed absorption candidate -/

/-- All kept descendants of a seed selection, including the seeds.
Backward inspection of the declared earlier parents gives a terminating
finite Boolean computation; the kept map itself supplies each edge proof.
This is graph reachability data, not choice from an existential path. -/
def HedgeWitness.keptDescendantNodes {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (seeds : NodeSet S) (child : Fin S.count) : Bool :=
  seeds child || finAny S.count (fun parent =>
    if _found : w.child parent = some child then w.keptDescendantNodes seeds parent else false)
termination_by child.val
decreasing_by exact S.directed_earlier (w.large_forest.child_edge parent child _found).2.2

theorem HedgeWitness.keptDescendantNodes_contains
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q) (seeds : NodeSet S) :
    NodeSet.Subset seeds (w.keptDescendantNodes seeds) := by
  intro child selected
  rw [HedgeWitness.keptDescendantNodes]
  exact Bool.or_eq_true_iff.mpr (.inl selected)

theorem HedgeWitness.keptDescendantNodes_closed
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q) (seeds : NodeSet S)
    (parent child : Fin S.count) (selected : w.keptDescendantNodes seeds parent = true)
    (found : w.child parent = some child) : w.keptDescendantNodes seeds child = true := by
  rw [HedgeWitness.keptDescendantNodes]
  apply Bool.or_eq_true_iff.mpr
  exact .inr (finAny_eq_true_of _ parent (by rw [dif_pos found]; exact selected))

theorem HedgeWitness.keptDescendantNodes_subset_large
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q) (seeds : NodeSet S)
    (within : NodeSet.Subset seeds w.large) : NodeSet.Subset (w.keptDescendantNodes seeds) w.large := by
  intro child selected
  rw [HedgeWitness.keptDescendantNodes] at selected
  cases Bool.or_eq_true_iff.mp selected with
  | inl seed => exact within child seed
  | inr reached =>
      rcases (finAny_eq_true_iff _).mp reached with ⟨parent, reaches⟩
      split at reaches
      · rename_i found
        exact (w.large_forest.child_edge parent child found).2.1
      · cases reaches

/-- Minimality is proved for arbitrary seed sets.  Thus the automatic
candidate does not add unrelated large vertices merely to make a route
permission test pass; any extra connectors must be explicitly justified. -/
theorem HedgeWitness.keptDescendantNodes_subset_of_closed
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q) (seeds nodes : NodeSet S)
    (contains : NodeSet.Subset seeds nodes)
    (closed : forall parent child, nodes parent = true -> w.child parent = some child -> nodes child = true)
    (child : Fin S.count) (selected : w.keptDescendantNodes seeds child = true) : nodes child = true := by
  rw [HedgeWitness.keptDescendantNodes] at selected
  cases Bool.or_eq_true_iff.mp selected with
  | inl seed => exact contains child seed
  | inr reached =>
      rcases (finAny_eq_true_iff _).mp reached with ⟨parent, reaches⟩
      split at reaches
      · rename_i found
        exact closed parent child
          (w.keptDescendantNodes_subset_of_closed seeds nodes contains closed parent reaches) found
      · cases reaches
termination_by child.val
decreasing_by exact S.directed_earlier (w.large_forest.child_edge parent child (by assumption)).2.2

/-- Start with the old small forest and all large-side route vertices,
then retain every successor needed by the original kept child map. -/
def HedgeWitness.routeAbsorbedSmall {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : NodeSet S :=
  w.keptDescendantNodes (NodeSet.union w.small (NodeSet.inter w.large w.rootReadoutNodes))

theorem HedgeWitness.routeAbsorbedSmall_contains_small
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q) :
    NodeSet.Subset w.small w.routeAbsorbedSmall :=
  (NodeSet.subset_union_left _ _).trans (w.keptDescendantNodes_contains _)

theorem HedgeWitness.routeAbsorbedSmall_subset_large
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q) :
    NodeSet.Subset w.routeAbsorbedSmall w.large := by
  apply w.keptDescendantNodes_subset_large
  intro node selected
  cases Bool.or_eq_true_iff.mp selected with
  | inl small => exact w.small_subset_large node small
  | inr routed => exact (Bool.and_eq_true_iff.mp routed).1

theorem HedgeWitness.routeAbsorbedSmall_contains_large_routes
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (node : Fin S.count) (inside : w.large node = true) (routed : w.rootReadoutNodes node = true) :
    w.routeAbsorbedSmall node = true :=
  w.keptDescendantNodes_contains _ node (Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr ⟨inside, routed⟩)))

/-- Every enlargement preserving the kept map and absorbing all large
route vertices contains the computed candidate.  Larger selections may add
bidirected connectors, but cannot omit a successor forced by the route. -/
theorem HedgeWitness.routeAbsorbedSmall_subset_of_enlargement
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q) (nodes : NodeSet S)
    (containsSmall : NodeSet.Subset w.small nodes)
    (childClosed : forall parent child, nodes parent = true -> w.child parent = some child -> nodes child = true)
    (containsRoutes : NodeSet.Subset (NodeSet.inter w.large w.rootReadoutNodes) nodes) :
    NodeSet.Subset w.routeAbsorbedSmall nodes := by
  apply w.keptDescendantNodes_subset_of_closed
  · intro node selected
    cases Bool.or_eq_true_iff.mp selected with
    | inl small => exact containsSmall node small
    | inr routed => exact containsRoutes node routed
  · exact childClosed

/-- Action avoidance of the least candidate is necessary for *any*
same-map absorption containing the old small forest.  A failing avoidance
test therefore cannot be repaired merely by adding more connector vertices.
This says nothing about changing the kept forest, choosing another hedge,
or building a different countermodel; those remain legitimate open routes. -/
theorem HedgeWitness.routeAbsorbedSmall_avoids_of_enlargement
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q) (nodes : NodeSet S)
    (containsSmall : NodeSet.Subset w.small nodes)
    (childClosed : forall parent child, nodes parent = true -> w.child parent = some child -> nodes child = true)
    (containsRoutes : NodeSet.Subset (NodeSet.inter w.large w.rootReadoutNodes) nodes)
    (avoids : NodeSet.Disjoint nodes q.action) : NodeSet.disjointBool w.routeAbsorbedSmall q.action = true := by
  apply (NodeSet.disjointBool_eq_true_iff _ _).mpr
  intro node selected
  exact avoids node (w.routeAbsorbedSmall_subset_of_enlargement nodes containsSmall childClosed containsRoutes node selected)

/-- Construct the absorbed witness after its two genuine finite checks.
All other forest obligations follow from the original witness and the
proved closure computation.  The original action and outcome are unchanged. -/
def HedgeWitness.absorbRouteVertices {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q)
    (connected : G.isSingleCComponent w.routeAbsorbedSmall = true)
    (avoids : NodeSet.disjointBool w.routeAbsorbedSmall q.action = true) : HedgeWitness G q :=
  w.enlargeSmall w.routeAbsorbedSmall w.routeAbsorbedSmall_contains_small w.routeAbsorbedSmall_subset_large
    (by
      rcases isSingleCComponent_spec G w.routeAbsorbedSmall connected with ⟨root, selected, equal⟩
      rw [equal]
      exact cComponentOf_is_component G _ selected)
    (w.keptDescendantNodes_closed _)
    ((NodeSet.disjointBool_eq_true_iff _ _).mp avoids)

/-- Every original outer route vertex is now a small vertex.  Non-large
route vertices remain outside, precisely matching the compensated theorem's
permission test.  No invalid update to the old carrier pair is used. -/
theorem HedgeWitness.absorbRouteVertices_routes_allowed
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (connected : G.isSingleCComponent w.routeAbsorbedSmall = true)
    (avoids : NodeSet.disjointBool w.routeAbsorbedSmall q.action = true) :
    forall node, (w.absorbRouteVertices connected avoids).rootReadoutNodes node = true ->
      (w.absorbRouteVertices connected avoids).small node = true ∨
        (w.absorbRouteVertices connected avoids).large node = false := by
  intro node routed
  change w.rootReadoutNodes node = true at routed
  cases inside : w.large node with
  | false => exact .inr inside
  | true => exact .inl (w.routeAbsorbedSmall_contains_large_routes node inside routed)

end Forests

/-! ## Positive countermodels for the unchanged original queries -/

section Countermodels

variable {S : ObservedSignature.{0}}

/-- Any connected, action-free, child-closed enlargement containing all
large route vertices supplies a positive original-query countermodel.
This general interface allows extra non-route connectors, not just the
minimal automatic candidate.  It constructs a new carrier pair indexed by
the enlarged forest; no equality of old and new countermodels is claimed. -/
noncomputable def HedgeWitness.positiveCounterexampleOfSmallEnlargement
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (nodes : NodeSet S)
    (containsSmall : NodeSet.Subset w.small nodes) (withinLarge : NodeSet.Subset nodes w.large)
    (connected : BidirectedComponent G nodes)
    (childClosed : forall parent child, nodes parent = true -> w.child parent = some child -> nodes child = true)
    (avoids : NodeSet.Disjoint nodes q.action)
    (containsRoutes : NodeSet.Subset (NodeSet.inter w.large w.rootReadoutNodes) nodes) :
    CounterexampleIn (GraphModelClass.positive G) q := by
  let enlarged := w.enlargeSmall nodes containsSmall withinLarge connected childClosed avoids
  apply enlarged.positiveCounterexampleOfSmallOrOutsideCarrierFlow rich
  intro node routed
  change w.rootReadoutNodes node = true at routed
  cases inside : w.large node with
  | false => exact .inr inside
  | true => exact .inl (containsRoutes node (Bool.and_eq_true_iff.mpr ⟨inside, routed⟩))

/-- The automatic candidate requires only its connectivity and action-
avoidance checks.  Positive noise, compatibility, full observational-law
equality, and separation under the original action are all constructed by
the existing compensated theorem on the absorbed witness. -/
noncomputable def HedgeWitness.positiveCounterexampleOfRouteAbsorption
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (connected : G.isSingleCComponent w.routeAbsorbedSmall = true)
    (avoids : NodeSet.disjointBool w.routeAbsorbedSmall q.action = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  (w.absorbRouteVertices connected avoids).positiveCounterexampleOfSmallOrOutsideCarrierFlow rich
    (w.absorbRouteVertices_routes_allowed connected avoids)

/-- Match the conditioning denominator in the same newly constructed
pair.  Parent closure can be proved against the original witness because
absorption changes neither original kept edges nor canonical flow edges.
The balancing vertex is allowed anywhere in the absorbed small forest,
including an originally outer-only route vertex or its kept descendant. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRouteAbsorptionOfParentClosed
    {G : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (connected : G.isSingleCComponent w.routeAbsorbedSmall = true)
    (avoids : NodeSet.disjointBool w.routeAbsorbedSmall query.action = true)
    (nodes : NodeSet S) (closed : w.CarrierFlowParentClosed nodes)
    (balance : Fin S.count) (inside : w.routeAbsorbedSmall balance = true) (omitted : nodes balance = false)
    (conditionWithin : NodeSet.Subset query.condition nodes) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  (w.absorbRouteVertices connected avoids).positiveConditionalCounterexampleOfCarrierFlowOfParentClosed rich
    (w.absorbRouteVertices_routes_allowed connected avoids) nodes closed balance inside omitted conditionWithin

/-- A topological prefix supplies closure without additional graph data.
The original conditioner may be a responding outer route row, now absorbed
into the new small forest; the balancing vertex must be later than it. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRouteAbsorptionOfConditionBeforeSmall
    {G : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (connected : G.isSingleCComponent w.routeAbsorbedSmall = true)
    (avoids : NodeSet.disjointBool w.routeAbsorbedSmall query.action = true)
    (balance : Fin S.count) (inside : w.routeAbsorbedSmall balance = true)
    (conditionBefore : forall node, query.condition node = true -> node.val < balance.val) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  w.positiveConditionalCounterexampleOfRouteAbsorptionOfParentClosed rich connected avoids
    (hedgeCarrierPrefixNodes balance) (w.carrierFlowParentClosed_prefix balance) balance inside
    (by simp only [hedgeCarrierPrefixNodes, Nat.lt_irrefl, decide_false])
    (fun node selected => decide_eq_true (conditionBefore node selected))

/-- Absorb the exact hedge extracted at an irreducible conditional
terminal, construct its matched-denominator pair, and restore the original
query along every certified exchange.  No fixed-depth failure unpacker or
assumed terminal non-identifiability is introduced. -/
noncomputable def ConditionalKernelFailure.counterexampleOfRouteAbsorbedParentClosedTerminal
    {G : ObservedGraph S} {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure G query fail) (rich : ObservedSignature.ValueRich S)
    (connected : G.isSingleCComponent failure.hedge.witness.routeAbsorbedSmall = true)
    (avoids : NodeSet.disjointBool failure.hedge.witness.routeAbsorbedSmall failure.terminal.action = true)
    (nodes : NodeSet S) (closed : failure.hedge.witness.CarrierFlowParentClosed nodes)
    (balance : Fin S.count) (inside : failure.hedge.witness.routeAbsorbedSmall balance = true)
    (omitted : nodes balance = false) (conditionWithin : NodeSet.Subset failure.terminal.condition nodes) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  failure.counterexampleOfTerminal (C := GraphModelClass.positive G) (fun member => member.2)
    (failure.hedge.witness.positiveConditionalCounterexampleOfRouteAbsorptionOfParentClosed rich connected avoids
      nodes closed balance inside omitted conditionWithin)

end Countermodels

end Causality
end Thesis
