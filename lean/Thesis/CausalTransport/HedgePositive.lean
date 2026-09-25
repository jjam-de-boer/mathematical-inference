import Thesis.CausalTransport.Soundness
import Thesis.CausalTransport.Completeness

namespace Thesis
namespace Causality

open Probability

/-!
# Positive hedge counterexamples detected through outcome marginals

`Completeness` provides both the complete-switch hedge mix and a one-root
variant localized to a selected bidirected edge.  Earlier composite-cylinder
separation asked every queried outcome to be a direct child of one action
seed.  That is stronger than semantic non-identifiability requires: equality
of the full outcome kernel would imply equality of every outcome marginal.

This module performs that reduction constructively.  It imports the finite
marginalization identity from `Soundness`, while keeping the two main theorem
development files independent of one another.  Pointwise `ValueEquivalent`
witnesses are hidden behind `Nonempty`; the marginal proof folds those
inhabited witnesses over the finite assignment enumeration and never chooses
a global witness family.

The strongest resulting leaf permits arbitrary additional query outcomes.  It
needs only one queried outcome and action parent joined by both a directed and
a bidirected edge.  Finite selectors choose the outcome and parent; the
bidirected edge canonically chooses its pair-root.  The right-hand model
changes only the pivot's structural equation, while the query continues to
intervene on its complete action set.  Thus neither unique-parent, odd-parity,
identical bidirected neighbourhoods, nor restrictions on unrelated action
vertices and outgoing edges are required.  The complete-switch construction
remains as an independent fallback.
-/

/-! ## The theorem-level marginal counterexample -/

/--
A directed-and-bidirected bow from an action pivot to one queried outcome is
already enough for a positive full-query counterexample.  The selected
pair-root is the root representing that bow.  Localizing the mix switch to
this root makes the two models observationally equal even when either endpoint
has arbitrary additional bidirected neighbours and the pivot has arbitrary
additional directed children.

As in the broader marginal construction below, equality of the complete query
would imply equality after restricting to `{y}`.  The one-root singleton
separation theorem contradicts that marginal equality.
-/
def hedgeSingleRootBowMarginalCounterexampleIn
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) {pivot y : Fin S.count}
    (parentSelected : q.action pivot = true)
    (directed : S.directed pivot y = true)
    (bidirected : G.bidirected pivot y = true)
    (outcomeSelected : q.outcome y = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  let root := pairRootBetween G bidirected
  let pivotMask := NodeSet.singleton pivot
  {
    left := hedgeSingleRootMixModel G rich root NodeSet.empty
    right := hedgeSingleRootMixModel G rich root pivotMask
    left_mem := hedgeSingleRootMixModel_mem_positive G rich root NodeSet.empty
    right_mem := hedgeSingleRootMixModel_mem_positive G rich root pivotMask
    observationally_equal :=
      hedgeSingleRootMixModel_observationally_equivalent_singleton G rich
        root pivot (hedgePairRootBetween_incident_left G bidirected)
    query_separated := by
      intro completeEquivalent
      let singletonOutcome := NodeSet.singleton y
      have singletonSubset : NodeSet.Subset singletonOutcome q.outcome :=
        NodeSet.singleton_subset_of_mem outcomeSelected
      let singletonQuery := q.restrictOutcome singletonOutcome singletonSubset
      have singletonEquivalent :
          singletonQuery.ValueEquivalent
            (hedgeSingleRootMixModel G rich root NodeSet.empty)
            (hedgeSingleRootMixModel G rich root pivotMask) := by
        exact JointKernelQuery.valueEquivalent_restrictOutcome q
          (hedgeSingleRootMixModel G rich root NodeSet.empty)
          (hedgeSingleRootMixModel G rich root pivotMask) completeEquivalent
          singletonOutcome singletonSubset
      have singletonSeparated :
          Not
            (singletonQuery.ValueEquivalent
              (hedgeSingleRootMixModel G rich root NodeSet.empty)
              (hedgeSingleRootMixModel G rich root pivotMask)) := by
        apply hedgeSingleRootSingletonOutcome_not_valueEquivalent G rich
          singletonQuery root
        · exact parentSelected
        · exact directed
        · simp [singletonQuery, singletonOutcome,
            JointKernelQuery.restrictOutcome, NodeSet.singleton]
        · intro candidate selected
          exact (NodeSet.singleton_eq_true_iff y candidate).mp selected
        · exact hedgePairRootBetween_incident_right G bidirected
      exact singletonSeparated singletonEquivalent
  }

/--
The positive singleton-pivot mix pair separates the complete query as soon as
it separates one selected outcome coordinate.  Assuming equality of the
complete kernel, finite marginalization restricts it to `{y}`; the
singleton-mask mix lemma then supplies the contradiction.

Only edges leaving `pivot` need preserve pair-root incidence.  This is enough
for observational equality because `pivot` is the sole member of the model's
switch mask.  Other action vertices still belong to the query intervention,
but their structural equations are identical in the two models.
-/
def hedgePivotSharedMarginalCounterexampleIn
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) {pivot y : Fin S.count}
    (root : Fin (pairRootCount G))
    (parentSelected : q.action pivot = true)
    (parentEdge : S.directed pivot y = true)
    (outcomeSeed : q.outcome y = true)
    (shared : forall child,
      S.directed pivot child = true →
        forall r,
          (hedgeLatentExtension G).incident (hedgePairRoot G r) pivot =
            (hedgeLatentExtension G).incident (hedgePairRoot G r) child)
    (incident :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
  CounterexampleIn (GraphModelClass.positive G) q where
  left := hedgeMixModel G rich NodeSet.empty
  right := hedgeMixModel G rich (NodeSet.singleton pivot)
  left_mem := hedgeMixModel_mem_positive G rich NodeSet.empty
  right_mem := hedgeMixModel_mem_positive G rich (NodeSet.singleton pivot)
  observationally_equal := by
    apply hedgeMixModel_observationally_equivalent_of_edge_shared_switch
    intro parent child inMask edge root
    have parentEq : parent = pivot :=
      (NodeSet.singleton_eq_true_iff pivot parent).mp inMask
    subst parent
    exact shared child edge root
  query_separated := by
    intro completeEquivalent
    let singletonOutcome := NodeSet.singleton y
    have singletonSubset : NodeSet.Subset singletonOutcome q.outcome :=
      NodeSet.singleton_subset_of_mem outcomeSeed
    let singletonQuery := q.restrictOutcome singletonOutcome singletonSubset
    have singletonEquivalent :
        singletonQuery.ValueEquivalent
          (hedgeMixModel G rich NodeSet.empty)
          (hedgeMixModel G rich (NodeSet.singleton pivot)) := by
      exact JointKernelQuery.valueEquivalent_restrictOutcome q
        (hedgeMixModel G rich NodeSet.empty)
        (hedgeMixModel G rich (NodeSet.singleton pivot)) completeEquivalent
        singletonOutcome singletonSubset
    have singletonSeparated :
        Not
          (singletonQuery.ValueEquivalent
            (hedgeMixModel G rich NodeSet.empty)
            (hedgeMixModel G rich (NodeSet.singleton pivot))) := by
      apply hedgeSingletonOutcome_not_valueEquivalent_of_singletonMask G rich
        singletonQuery root
      · exact parentSelected
      · exact parentEdge
      · simp [singletonQuery, singletonOutcome,
          JointKernelQuery.restrictOutcome, NodeSet.singleton]
      · intro candidate selected
        exact (NodeSet.singleton_eq_true_iff y candidate).mp selected
      · exact incident
    exact singletonSeparated singletonEquivalent

/--
Compatibility form with the earlier, stronger hypothesis that every edge
leaving the query action preserves pair-root incidence.  The implementation
now uses only the selected pivot's edges and a singleton model mask.
-/
def hedgeEdgeSharedMarginalCounterexampleIn
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) {pivot y : Fin S.count}
    (root : Fin (pairRootCount G))
    (parentSelected : q.action pivot = true)
    (parentEdge : S.directed pivot y = true)
    (outcomeSeed : q.outcome y = true)
    (shared : forall parent child,
      q.action parent = true → S.directed parent child = true →
        forall r,
          (hedgeLatentExtension G).incident (hedgePairRoot G r) parent =
            (hedgeLatentExtension G).incident (hedgePairRoot G r) child)
    (incident :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  hedgePivotSharedMarginalCounterexampleIn G rich q root parentSelected
    parentEdge outcomeSeed
    (fun child edge r => shared pivot child parentSelected edge r) incident

/-! ## Executable readiness and failure-pipeline integration -/

/-- Whether `child` has a parent in the action that also forms a bidirected bow. -/
def bowActionParentExistsBool (G : ObservedGraph S)
    (action : NodeSet S) (child : Fin S.count) : Bool :=
  (NodeSet.enumerated S).any fun parent =>
    action parent && (S.directed parent child && G.bidirected parent child)

/-- First action parent witnessing a directed-and-bidirected bow into `child`. -/
def firstBowActionParent (G : ObservedGraph S)
    (action : NodeSet S) (child : Fin S.count)
    (existsParent : bowActionParentExistsBool G action child = true) :
    Fin S.count :=
  listFirstAny (NodeSet.enumerated S)
    (fun parent =>
      action parent && (S.directed parent child && G.bidirected parent child))
    existsParent

theorem firstBowActionParent_selected (G : ObservedGraph S)
    (action : NodeSet S) (child : Fin S.count)
    (existsParent : bowActionParentExistsBool G action child = true) :
    action (firstBowActionParent G action child existsParent) = true :=
  (Bool.and_eq_true_iff.mp
    (listFirstAny_pred (NodeSet.enumerated S)
      (fun parent =>
        action parent &&
          (S.directed parent child && G.bidirected parent child))
      existsParent)).1

theorem firstBowActionParent_directed (G : ObservedGraph S)
    (action : NodeSet S) (child : Fin S.count)
    (existsParent : bowActionParentExistsBool G action child = true) :
    S.directed (firstBowActionParent G action child existsParent) child = true :=
  (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp
      (listFirstAny_pred (NodeSet.enumerated S)
        (fun parent =>
          action parent &&
            (S.directed parent child && G.bidirected parent child))
        existsParent)).2).1

theorem firstBowActionParent_bidirected (G : ObservedGraph S)
    (action : NodeSet S) (child : Fin S.count)
    (existsParent : bowActionParentExistsBool G action child = true) :
    G.bidirected (firstBowActionParent G action child existsParent) child =
      true :=
  (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp
      (listFirstAny_pred (NodeSet.enumerated S)
        (fun parent =>
          action parent &&
            (S.directed parent child && G.bidirected parent child))
        existsParent)).2).2

/-- Local bow readiness at one candidate query outcome. -/
def hedgeMarginalBowOutcomeReadyBool (G : ObservedGraph S)
    (q : JointKernelQuery S) (outcome : Fin S.count) : Bool :=
  q.outcome outcome && bowActionParentExistsBool G q.action outcome

/-- Whether any queried outcome has an action parent forming a bow. -/
def hedgeMarginalBowQueryReady (G : ObservedGraph S)
    (q : JointKernelQuery S) : Bool :=
  (NodeSet.enumerated S).any (hedgeMarginalBowOutcomeReadyBool G q)

/-- First queried outcome accepted by the bow-marginal test. -/
def firstHedgeMarginalBowOutcome (G : ObservedGraph S)
    (q : JointKernelQuery S)
    (ready : hedgeMarginalBowQueryReady G q = true) : Fin S.count :=
  listFirstAny (NodeSet.enumerated S)
    (hedgeMarginalBowOutcomeReadyBool G q) ready

theorem firstHedgeMarginalBowOutcome_in_outcome (G : ObservedGraph S)
    (q : JointKernelQuery S)
    (ready : hedgeMarginalBowQueryReady G q = true) :
    q.outcome (firstHedgeMarginalBowOutcome G q ready) = true :=
  (Bool.and_eq_true_iff.mp
    (listFirstAny_pred (NodeSet.enumerated S)
      (hedgeMarginalBowOutcomeReadyBool G q) ready)).1

theorem firstHedgeMarginalBowOutcome_parent_ready (G : ObservedGraph S)
    (q : JointKernelQuery S)
    (ready : hedgeMarginalBowQueryReady G q = true) :
    bowActionParentExistsBool G q.action
        (firstHedgeMarginalBowOutcome G q ready) = true :=
  (Bool.and_eq_true_iff.mp
    (listFirstAny_pred (NodeSet.enumerated S)
      (hedgeMarginalBowOutcomeReadyBool G q) ready)).2

/-- Query-wide bow readiness packages the root-local positive counterexample. -/
def hedgeSingleRootBowMarginalCounterexampleIn_of_query_ready
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S)
    (ready : hedgeMarginalBowQueryReady G q = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  let outcome := firstHedgeMarginalBowOutcome G q ready
  let parentReady := firstHedgeMarginalBowOutcome_parent_ready G q ready
  hedgeSingleRootBowMarginalCounterexampleIn G rich q
    (firstBowActionParent_selected G q.action outcome parentReady)
    (firstBowActionParent_directed G q.action outcome parentReady)
    (firstBowActionParent_bidirected G q.action outcome parentReady)
    (firstHedgeMarginalBowOutcome_in_outcome G q ready)

/-- Whether `child` has at least one directed parent in the action set. -/
def actionParentExistsBool (action : NodeSet S) (child : Fin S.count) : Bool :=
  (NodeSet.enumerated S).any fun parent =>
    action parent && S.directed parent child

theorem actionParentExistsBool_eq_true_of
    (action : NodeSet S) {parent child : Fin S.count}
    (selected : action parent = true)
    (edge : S.directed parent child = true) :
    actionParentExistsBool action child = true :=
  List.any_eq_true.mpr
    ⟨parent, NodeSet.mem_enumerated S parent, by simp [selected, edge]⟩

/--
The first action parent of `child`, recovered from the finite node
enumeration after the executable existence test succeeds.
-/
def firstActionParent (action : NodeSet S) (child : Fin S.count)
    (existsParent : actionParentExistsBool action child = true) :
    Fin S.count :=
  listFirstAny (NodeSet.enumerated S)
    (fun parent => action parent && S.directed parent child) existsParent

theorem firstActionParent_selected
    (action : NodeSet S) (child : Fin S.count)
    (existsParent : actionParentExistsBool action child = true) :
    action (firstActionParent action child existsParent) = true :=
  (Bool.and_eq_true_iff.mp
    (listFirstAny_pred (NodeSet.enumerated S)
      (fun parent => action parent && S.directed parent child)
      existsParent)).1

theorem firstActionParent_directed
    (action : NodeSet S) (child : Fin S.count)
    (existsParent : actionParentExistsBool action child = true) :
    S.directed (firstActionParent action child existsParent) child = true :=
  (Bool.and_eq_true_iff.mp
    (listFirstAny_pred (NodeSet.enumerated S)
      (fun parent => action parent && S.directed parent child)
      existsParent)).2

/-!
The localized countermodel must select a parent whose own outgoing edges
preserve the pair-root switch.  Folding that requirement into the finite
search is important: choosing the first action parent and testing it
afterwards could miss a later suitable parent.
-/

/-- Whether `child` has a directed action parent with shared-switch children. -/
def sharedSwitchActionParentExistsBool (G : ObservedGraph S)
    (action : NodeSet S) (child : Fin S.count) : Bool :=
  (NodeSet.enumerated S).any fun parent =>
    action parent &&
      (S.directed parent child && sharedSwitchChildrenBool G parent)

/--
The first suitable shared-switch action parent, obtained from the finite node
enumeration.  The proof argument certifies that the search cannot be empty;
the selected vertex itself remains computational data.
-/
def firstSharedSwitchActionParent (G : ObservedGraph S)
    (action : NodeSet S) (child : Fin S.count)
    (existsParent :
      sharedSwitchActionParentExistsBool G action child = true) :
    Fin S.count :=
  listFirstAny (NodeSet.enumerated S)
    (fun parent =>
      action parent &&
        (S.directed parent child && sharedSwitchChildrenBool G parent))
    existsParent

theorem firstSharedSwitchActionParent_selected (G : ObservedGraph S)
    (action : NodeSet S) (child : Fin S.count)
    (existsParent :
      sharedSwitchActionParentExistsBool G action child = true) :
    action (firstSharedSwitchActionParent G action child existsParent) = true :=
  (Bool.and_eq_true_iff.mp
    (listFirstAny_pred (NodeSet.enumerated S)
      (fun parent =>
        action parent &&
          (S.directed parent child && sharedSwitchChildrenBool G parent))
      existsParent)).1

theorem firstSharedSwitchActionParent_directed (G : ObservedGraph S)
    (action : NodeSet S) (child : Fin S.count)
    (existsParent :
      sharedSwitchActionParentExistsBool G action child = true) :
    S.directed (firstSharedSwitchActionParent G action child existsParent)
        child = true :=
  (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp
      (listFirstAny_pred (NodeSet.enumerated S)
        (fun parent =>
          action parent &&
            (S.directed parent child && sharedSwitchChildrenBool G parent))
        existsParent)).2).1

theorem firstSharedSwitchActionParent_children (G : ObservedGraph S)
    (action : NodeSet S) (child : Fin S.count)
    (existsParent :
      sharedSwitchActionParentExistsBool G action child = true) :
    sharedSwitchChildrenBool G
        (firstSharedSwitchActionParent G action child existsParent) = true :=
  (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp
      (listFirstAny_pred (NodeSet.enumerated S)
        (fun parent =>
          action parent &&
            (S.directed parent child && sharedSwitchChildrenBool G parent))
        existsParent)).2).2

/-- A global action-edge shared-switch test supplies the local pivot test. -/
theorem sharedSwitchChildrenBool_of_actionEdgesSharePairRootSwitchBool
    (G : ObservedGraph S) (action : NodeSet S) {parent : Fin S.count}
    (shared : actionEdgesSharePairRootSwitchBool G action = true)
    (selected : action parent = true) :
    sharedSwitchChildrenBool G parent = true := by
  have parentOk :=
    (List.all_eq_true.mp shared) parent (NodeSet.mem_enumerated S parent)
  simpa [actionEdgesSharePairRootSwitchBool, sharedSwitchChildrenBool,
    selected] using parentOk

/-!
### Selecting the marginal coordinate

The hedge extractor stores one reachable outcome for constructions that need
a canonical sink.  Marginal separation is less rigid: any queried coordinate
with the local pivot geometry suffices.  The following second finite search
therefore ranges over the complete outcome set instead of committing to the
stored seed.  This matters when the stored outcome has no usable parent but a
different queried coordinate does.
-/

/-- Local singleton-pivot readiness at one candidate outcome coordinate. -/
def hedgeMarginalPivotOutcomeReadyBool (G : ObservedGraph S)
    (q : JointKernelQuery S) (outcome : Fin S.count) : Bool :=
  q.outcome outcome &&
    (sharedSwitchActionParentExistsBool G q.action outcome &&
      (List.finRange (pairRootCount G)).any (fun root =>
        (hedgeLatentExtension G).incident (hedgePairRoot G root) outcome))

/--
Whether some queried outcome admits the localized marginal construction.
-/
def hedgeMarginalPivotQueryReady (G : ObservedGraph S)
    (q : JointKernelQuery S) : Bool :=
  (NodeSet.enumerated S).any (hedgeMarginalPivotOutcomeReadyBool G q)

/-- First query outcome accepted by the localized marginal test. -/
def firstHedgeMarginalPivotOutcome (G : ObservedGraph S)
    (q : JointKernelQuery S)
    (ready : hedgeMarginalPivotQueryReady G q = true) : Fin S.count :=
  listFirstAny (NodeSet.enumerated S)
    (hedgeMarginalPivotOutcomeReadyBool G q) ready

/-- The selected marginal coordinate really belongs to the query outcome. -/
theorem firstHedgeMarginalPivotOutcome_in_outcome (G : ObservedGraph S)
    (q : JointKernelQuery S)
    (ready : hedgeMarginalPivotQueryReady G q = true) :
    q.outcome (firstHedgeMarginalPivotOutcome G q ready) = true :=
  (Bool.and_eq_true_iff.mp
    (listFirstAny_pred (NodeSet.enumerated S)
      (hedgeMarginalPivotOutcomeReadyBool G q) ready)).1

/-- The selected marginal coordinate has a suitable shared-switch parent. -/
theorem firstHedgeMarginalPivotOutcome_parent_ready
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (ready : hedgeMarginalPivotQueryReady G q = true) :
    sharedSwitchActionParentExistsBool G q.action
        (firstHedgeMarginalPivotOutcome G q ready) = true :=
  (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp
      (listFirstAny_pred (NodeSet.enumerated S)
        (hedgeMarginalPivotOutcomeReadyBool G q) ready)).2).1

/-- The selected marginal coordinate carries a nonconstant pair-root switch. -/
theorem firstHedgeMarginalPivotOutcome_incident_ready
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (ready : hedgeMarginalPivotQueryReady G q = true) :
    (List.finRange (pairRootCount G)).any (fun root =>
      (hedgeLatentExtension G).incident (hedgePairRoot G root)
        (firstHedgeMarginalPivotOutcome G q ready)) = true :=
  (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp
      (listFirstAny_pred (NodeSet.enumerated S)
        (hedgeMarginalPivotOutcomeReadyBool G q) ready)).2).2

/-- Query-wide readiness directly packages the localized counterexample. -/
def hedgeMarginalPivotCounterexampleIn_of_query_ready
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S)
    (ready : hedgeMarginalPivotQueryReady G q = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  let outcome := firstHedgeMarginalPivotOutcome G q ready
  let parentReady :=
    firstHedgeMarginalPivotOutcome_parent_ready G q ready
  let incidentReady :=
    firstHedgeMarginalPivotOutcome_incident_ready G q ready
  hedgePivotSharedMarginalCounterexampleIn G rich q
    (firstIncidentPairRoot G outcome incidentReady)
    (firstSharedSwitchActionParent_selected G q.action outcome parentReady)
    (firstSharedSwitchActionParent_directed G q.action outcome parentReady)
    (firstHedgeMarginalPivotOutcome_in_outcome G q ready)
    (fun _child edge root =>
      sharedSwitchChildrenBool_hedgeIncident
        (firstSharedSwitchActionParent_children G q.action outcome parentReady)
        edge root)
    (firstIncidentPairRoot_incident G outcome incidentReady)

/--
Boolean readiness for the marginal edge-shared leaf.  Unlike
`hedgeWitnessEdgeSharedReady`, it imposes no shape restriction on outcomes
other than the existence of an action parent at the stored seed: unrelated
queried coordinates are removed by finite marginalization before singleton
separation.
-/
def hedgeWitnessMarginalEdgeSharedReady (G : ObservedGraph S)
    (q : JointKernelQuery S) (w : HedgeWitness G q) : Bool :=
  actionParentExistsBool q.action w.outcomeSeed &&
    (actionEdgesSharePairRootSwitchBool G q.action &&
      (List.finRange (pairRootCount G)).any (fun root =>
        (hedgeLatentExtension G).incident (hedgePairRoot G root)
          w.outcomeSeed))

/--
The earlier all-outcomes edge-shared test is contained in the marginal test.
Its stored action-seed edge supplies an action parent of the selected outcome;
the outcome-subset and unique-parent scans are no longer needed after
marginalization and the pivot assignment.
-/
theorem hedgeWitnessMarginalEdgeSharedReady_of_edgeSharedReady
    (G : ObservedGraph S) (q : JointKernelQuery S) (w : HedgeWitness G q)
    (ready : hedgeWitnessEdgeSharedReady G q w = true) :
    hedgeWitnessMarginalEdgeSharedReady G q w = true := by
  let actionSeed := (Bool.and_eq_true_iff.mp ready).1
  let rest := (Bool.and_eq_true_iff.mp ready).2
  let _outcomes := (Bool.and_eq_true_iff.mp rest).1
  let rest2 := (Bool.and_eq_true_iff.mp rest).2
  let _unique := (Bool.and_eq_true_iff.mp rest2).1
  let rest3 := (Bool.and_eq_true_iff.mp rest2).2
  let directed := (Bool.and_eq_true_iff.mp rest3).1
  let rest4 := (Bool.and_eq_true_iff.mp rest3).2
  let shared := (Bool.and_eq_true_iff.mp rest4).1
  let incident := (Bool.and_eq_true_iff.mp rest4).2
  have parentExists :
      actionParentExistsBool q.action w.outcomeSeed = true :=
    actionParentExistsBool_eq_true_of q.action actionSeed directed
  exact Bool.and_eq_true_iff.mpr ⟨parentExists,
    Bool.and_eq_true_iff.mpr ⟨shared, incident⟩⟩

/--
Localized readiness for the marginal pivot leaf.  It asks for one suitable
action parent of the stored outcome, rather than imposing the shared-switch
condition on the complete action set.  The second conjunct selects an
incident pair-root that makes the singleton outcome probability separate.
-/
def hedgeWitnessMarginalPivotReady (G : ObservedGraph S)
    (q : JointKernelQuery S) (w : HedgeWitness G q) : Bool :=
  sharedSwitchActionParentExistsBool G q.action w.outcomeSeed &&
    (List.finRange (pairRootCount G)).any (fun root =>
      (hedgeLatentExtension G).incident (hedgePairRoot G root)
        w.outcomeSeed)

/--
Readiness at the extractor's stored outcome is contained in the query-wide
search.  This lemma records the coverage relation explicitly, so replacing
the old search cannot silently lose any established case.
-/
theorem hedgeMarginalPivotQueryReady_of_witness_ready
    (G : ObservedGraph S) (q : JointKernelQuery S) (w : HedgeWitness G q)
    (ready : hedgeWitnessMarginalPivotReady G q w = true) :
    hedgeMarginalPivotQueryReady G q = true := by
  have parentReady := (Bool.and_eq_true_iff.mp ready).1
  have incidentReady := (Bool.and_eq_true_iff.mp ready).2
  apply List.any_eq_true.mpr
  refine ⟨w.outcomeSeed, NodeSet.mem_enumerated S w.outcomeSeed, ?_⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨w.outcomeSeed_in_outcome,
      Bool.and_eq_true_iff.mpr ⟨parentReady, incidentReady⟩⟩

/-- The former global marginal test implies the localized pivot test. -/
theorem hedgeWitnessMarginalPivotReady_of_marginalEdgeSharedReady
    (G : ObservedGraph S) (q : JointKernelQuery S) (w : HedgeWitness G q)
    (ready : hedgeWitnessMarginalEdgeSharedReady G q w = true) :
    hedgeWitnessMarginalPivotReady G q w = true := by
  let parentExists := (Bool.and_eq_true_iff.mp ready).1
  let rest := (Bool.and_eq_true_iff.mp ready).2
  let shared := (Bool.and_eq_true_iff.mp rest).1
  let incident := (Bool.and_eq_true_iff.mp rest).2
  let pivot := firstActionParent q.action w.outcomeSeed parentExists
  have selected : q.action pivot = true :=
    firstActionParent_selected q.action w.outcomeSeed parentExists
  have directed : S.directed pivot w.outcomeSeed = true :=
    firstActionParent_directed q.action w.outcomeSeed parentExists
  have children : sharedSwitchChildrenBool G pivot = true :=
    sharedSwitchChildrenBool_of_actionEdgesSharePairRootSwitchBool
      G q.action shared selected
  have suitable :
      sharedSwitchActionParentExistsBool G q.action w.outcomeSeed = true :=
    List.any_eq_true.mpr
      ⟨pivot, NodeSet.mem_enumerated S pivot,
        by simp [selected, directed, children]⟩
  exact Bool.and_eq_true_iff.mpr ⟨suitable, incident⟩

/-- The original all-outcomes readiness also implies the localized test. -/
theorem hedgeWitnessMarginalPivotReady_of_edgeSharedReady
    (G : ObservedGraph S) (q : JointKernelQuery S) (w : HedgeWitness G q)
    (ready : hedgeWitnessEdgeSharedReady G q w = true) :
    hedgeWitnessMarginalPivotReady G q w = true :=
  hedgeWitnessMarginalPivotReady_of_marginalEdgeSharedReady G q w
    (hedgeWitnessMarginalEdgeSharedReady_of_edgeSharedReady G q w ready)

/-- Localized readiness packages the singleton-pivot counterexample. -/
def hedgePivotSharedMarginalCounterexampleIn_of_ready
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) (w : HedgeWitness G q)
    (ready : hedgeWitnessMarginalPivotReady G q w = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  let parentExists := (Bool.and_eq_true_iff.mp ready).1
  let incident := (Bool.and_eq_true_iff.mp ready).2
  hedgePivotSharedMarginalCounterexampleIn G rich q
    (firstIncidentPairRoot G w.outcomeSeed incident)
    (firstSharedSwitchActionParent_selected G q.action w.outcomeSeed
      parentExists)
    (firstSharedSwitchActionParent_directed G q.action w.outcomeSeed
      parentExists)
    w.outcomeSeed_in_outcome
    (fun _child edge root =>
      sharedSwitchChildrenBool_hedgeIncident
        (firstSharedSwitchActionParent_children G q.action w.outcomeSeed
          parentExists)
        edge root)
    (firstIncidentPairRoot_incident G w.outcomeSeed incident)

/-- Readiness of a witness packages the generalized positive counterexample. -/
def hedgeEdgeSharedMarginalCounterexampleIn_of_ready
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) (w : HedgeWitness G q)
    (ready : hedgeWitnessMarginalEdgeSharedReady G q w = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  let parentExists := (Bool.and_eq_true_iff.mp ready).1
  let rest := (Bool.and_eq_true_iff.mp ready).2
  let shared := (Bool.and_eq_true_iff.mp rest).1
  let incident := (Bool.and_eq_true_iff.mp rest).2
  hedgeEdgeSharedMarginalCounterexampleIn G rich q
    (firstIncidentPairRoot G w.outcomeSeed incident)
    (firstActionParent_selected q.action w.outcomeSeed parentExists)
    (firstActionParent_directed q.action w.outcomeSeed parentExists)
    w.outcomeSeed_in_outcome
    (fun _parent _child selected edge root =>
      actionEdgesSharePairRootSwitchBool_hedgeIncident shared selected edge
        root)
    (firstIncidentPairRoot_incident G w.outcomeSeed incident)

/--
Enhanced executable positive counterexample search.  The root-local bow leaf
is tried first because it tolerates arbitrary extra directed children and
bidirected arms.  The complete-switch marginal leaf remains as an independent
fallback, followed by the original seed-based search.
-/
def hedgePositiveCounterexampleIn? (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (w : HedgeWitness G q) :
    Option (CounterexampleIn (GraphModelClass.positive G) q) :=
  if bowReady : hedgeMarginalBowQueryReady G q = true then
    some
      (hedgeSingleRootBowMarginalCounterexampleIn_of_query_ready G rich q
        bowReady)
  else if pivotReady : hedgeMarginalPivotQueryReady G q = true then
    some
      (hedgeMarginalPivotCounterexampleIn_of_query_ready G rich q pivotReady)
  else
    hedgeCounterexampleIn? G rich q w

theorem hedgePositiveCounterexampleIn?_isSome_iff
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) (w : HedgeWitness G q) :
    (hedgePositiveCounterexampleIn? G rich q w).isSome =
      (hedgeMarginalBowQueryReady G q ||
        (hedgeMarginalPivotQueryReady G q ||
          (hedgeCounterexampleIn? G rich q w).isSome)) := by
  dsimp [hedgePositiveCounterexampleIn?]
  split
  · next ready => simp [ready]
  · next notReady =>
      simp [notReady]
      split
      · next ready => simp [ready]
      · next notReady => simp [notReady]

/-- Apply the enhanced positive search after constructive hedge extraction. -/
def hedgePositiveCounterexample? (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (failure : IdentificationFail S) :
    Option (CounterexampleIn (GraphModelClass.positive G) q) :=
  match hedgeWitness? G q failure with
  | none => none
  | some witness => hedgePositiveCounterexampleIn? G rich q witness

end Causality
end Thesis
