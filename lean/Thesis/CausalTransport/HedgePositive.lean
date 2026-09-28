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

/-! ## Full-alphabet carriers for a Boolean hedge signal -/

/-- Emit a Boolean hedge bit without collapsing the rest of an observed
coordinate's finite alphabet.

`second` is reserved for bit one.  At bit zero the supplied background value
is retained, except that a `second` background is moved to `first`.  Thus the
output's `hedgeIsSecond` bit is exactly `bit`, while every observed value can
still be reconstructed by supplying that value as the background and taking
its own `hedgeIsSecond` bit.  This is the finite-alphabet replacement for the
binary-only `hedgeParityValue`; it uses the two values stored in `ValueRich`
as data and performs no propositional selection. -/
def hedgeParityCarrierValue (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (bit : Bool) (background : S.Value child) :
    S.Value child :=
  if bit then rich.second child
  else if background = rich.second child then rich.first child else background

/-- Reading the distinguished bit from a carrier recovers its Boolean input,
independently of the background label. -/
theorem hedgeIsSecond_parityCarrierValue
    (rich : ObservedSignature.ValueRich S) (child : Fin S.count)
    (bit : Bool) (background : S.Value child) :
    hedgeIsSecond rich child
      (hedgeParityCarrierValue rich child bit background) = bit := by
  cases bit with
  | false =>
      by_cases second : background = rich.second child
      · simp [hedgeParityCarrierValue, second, hedgeIsSecond,
          rich.different]
      · simp [hedgeParityCarrierValue, second, hedgeIsSecond]
  | true =>
      simp [hedgeParityCarrierValue, hedgeIsSecond]

/-- A value is recovered exactly when it supplies both the carrier background
and the bit saying whether it is the distinguished `second` value.  This is
the constructive surjectivity fact used by the eventual positive hedge
models. -/
theorem hedgeParityCarrierValue_reconstruct
    (rich : ObservedSignature.ValueRich S) (child : Fin S.count)
    (value : S.Value child) :
    hedgeParityCarrierValue rich child (hedgeIsSecond rich child value) value =
      value := by
  by_cases second : value = rich.second child
  · subst value
    simp [hedgeParityCarrierValue, hedgeIsSecond]
  · simp [hedgeParityCarrierValue, hedgeIsSecond, second]

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

/-! ## Biased defect softening of the general root-parity construction -/

/-!
The faithful large/small parity models in `Completeness` use an all-ones
product prior and deterministic even-incidence equations.  They provide the
general hedge separation, but their observational laws omit one parity class.
The definitions below add a private *defect bit* at one common root.  A biased,
strictly positive private prior makes both defect values possible without
making them equiprobable; XOR with an equiprobable defect would erase the
interventional parity gap.

Every definition remains finite data.  The distinguished private index is
`0`, available because every observed value enumeration is nonempty.  Pair
roots retain unit weights, while every nonzero private index receives weight
two.  Thus all latent atoms remain positive and the zero-index defect has
strictly less than half of the private mass even for a binary observed node.
-/

/-!
### A separate private defect coordinate

The background label and the parity defect must be independently selectable.
Using the old private enumeration index for both would fail to realize some
non-`second` targets with the required defect parity.  We therefore prefix one
Boolean latent root, incident only to `defectNode`.  Prefixing is deliberate:
`Fin.cases` and its zero/successor reduction laws are constructive, whereas
the library theorem reducing `Fin.lastCases` at `castSucc` depends on
`Classical.choice`.  The coordinate order has no semantic significance, and
a root with one child creates no projected bidirected edge.
-/

/-- The hedge skeleton plus one private Boolean defect root. -/
def hedgeDefectLatentCount (G : ObservedGraph S) : Nat :=
  hedgeLatentCount G + 1

/-- The distinguished zero coordinate of the augmented latent family.  Naming
it avoids asking typeclass inference to rediscover that the opaque count is
positive each time the defect is read. -/
def hedgeDefectRoot (G : ObservedGraph S) :
    Fin (hedgeDefectLatentCount G) :=
  ⟨0, by simp [hedgeDefectLatentCount]⟩

/-- The zero coordinate is the new Boolean defect; successor coordinates
retain the corresponding old hedge-root types. -/
def hedgeDefectLatentValue (G : ObservedGraph S)
    (root : Fin (hedgeDefectLatentCount G)) : Type :=
  Fin.cases Bool (fun old => hedgeLatentValue G old) root

@[simp] theorem hedgeDefectLatentValue_zero (G : ObservedGraph S) :
    hedgeDefectLatentValue G (hedgeDefectRoot G) = Bool := by
  simp [hedgeDefectLatentValue, hedgeDefectRoot, hedgeDefectLatentCount]

@[simp] theorem hedgeDefectLatentValue_succ (G : ObservedGraph S)
    (root : Fin (hedgeLatentCount G)) :
    hedgeDefectLatentValue G root.succ = hedgeLatentValue G root := by
  simp [hedgeDefectLatentValue, hedgeDefectLatentCount]

instance hedgeDefectLatentValueDecidableEq (G : ObservedGraph S)
    (root : Fin (hedgeDefectLatentCount G)) :
    DecidableEq (hedgeDefectLatentValue G root) := by
  refine Fin.cases
    (motive := fun root => DecidableEq (hedgeDefectLatentValue G root))
    ?_ (fun old => ?_) root
  · change DecidableEq
      (hedgeDefectLatentValue G (hedgeDefectRoot G))
    rw [hedgeDefectLatentValue_zero]
    infer_instance
  · change DecidableEq (hedgeDefectLatentValue G old.succ)
    rw [hedgeDefectLatentValue_succ]
    infer_instance

instance hedgeDefectAssignmentDecidableEq (G : ObservedGraph S) :
    DecidableEq ((root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :=
  FiniteProduct.assignmentDecidableEq (hedgeDefectLatentCount G)
    (hedgeDefectLatentValue G) (fun _root => inferInstance)

/-- Enumerate the defect coordinate by both Boolean values and reuse every
old hedge enumeration verbatim. -/
def hedgeDefectLatentEnum (G : ObservedGraph S)
    (root : Fin (hedgeDefectLatentCount G)) :
    List (hedgeDefectLatentValue G root) :=
  Fin.cases
    (cast (congrArg List (hedgeDefectLatentValue_zero G).symm)
      [false, true])
    (fun old =>
      cast (congrArg List (hedgeDefectLatentValue_succ G old).symm)
        (hedgeLatentEnum G old))
    root

/-- Every value of the augmented latent extension occurs in its explicit
enumeration. -/
theorem hedgeDefectLatentEnum_complete (G : ObservedGraph S)
    (root : Fin (hedgeDefectLatentCount G))
    (value : hedgeDefectLatentValue G root) :
    value ∈ hedgeDefectLatentEnum G root := by
  refine Fin.cases
    (motive := fun root => forall value : hedgeDefectLatentValue G root,
      value ∈ hedgeDefectLatentEnum G root)
    ?_ (fun old => ?_) root value
  · intro bit
    have member :
        bit ∈ cast (congrArg List (hedgeDefectLatentValue_zero G).symm)
          [false, true] := by
      apply (mem_cast_list (hedgeDefectLatentValue_zero G).symm
        [false, true] bit).mpr
      have transported : Bool := cast (hedgeDefectLatentValue_zero G) bit
      cases transported <;> simp
    simpa [hedgeDefectLatentEnum, hedgeDefectLatentCount] using member
  · intro oldValue
    have member :=
      (mem_cast_list (hedgeDefectLatentValue_succ G old).symm
        (hedgeLatentEnum G old) oldValue).mpr
          (hedgeLatentEnum_complete G old
            (cast (hedgeDefectLatentValue_succ G old) oldValue))
    simpa [hedgeDefectLatentEnum, hedgeDefectLatentCount] using member

/-- The prefixed root is private to `defectNode`; all earlier incidence is
the original hedge incidence. -/
def hedgeDefectIncident (G : ObservedGraph S) (defectNode : Fin S.count)
    (root : Fin (hedgeDefectLatentCount G)) (child : Fin S.count) : Bool :=
  Fin.cases (decide (child = defectNode))
    (fun old => hedgeIncident G old child) root

/-- Latent extension used by the full-support parity softening. -/
def hedgeDefectLatentExtension (G : ObservedGraph S)
    (defectNode : Fin S.count) : LatentExtension S where
  count := hedgeDefectLatentCount G
  Value := hedgeDefectLatentValue G
  valueEnumeration := hedgeDefectLatentEnum G
  value_complete := hedgeDefectLatentEnum_complete G
  valueDecidableEq := fun root => by
    refine Fin.cases
      (motive := fun root => DecidableEq (hedgeDefectLatentValue G root))
      ?_ (fun old => ?_) root
    · change DecidableEq
        (hedgeDefectLatentValue G (hedgeDefectRoot G))
      rw [hedgeDefectLatentValue_zero]
      infer_instance
    · change DecidableEq (hedgeDefectLatentValue G old.succ)
      rw [hedgeDefectLatentValue_succ]
      infer_instance
  incident := hedgeDefectIncident G defectNode

@[simp] theorem hedgeDefectIncident_succ (G : ObservedGraph S)
    (defectNode : Fin S.count) (root : Fin (hedgeLatentCount G))
    (child : Fin S.count) :
    hedgeDefectIncident G defectNode root.succ child =
      hedgeIncident G root child := by
  simp [hedgeDefectIncident, hedgeDefectLatentCount]

@[simp] theorem hedgeDefectIncident_zero (G : ObservedGraph S)
    (defectNode child : Fin S.count) :
    hedgeDefectIncident G defectNode
        (hedgeDefectRoot G) child =
      decide (child = defectNode) := by
  simp [hedgeDefectIncident, hedgeDefectRoot, hedgeDefectLatentCount]

/-- Adding a one-child source leaves the projected bidirected graph
unchanged.  The proof eliminates an augmented root into the private zero
coordinate or an old successor coordinate.  If the private coordinate met
two distinct observed nodes, both would equal its unique child. -/
theorem hedgeDefectLatentExtension_projected (G : ObservedGraph S)
    (defectNode i j : Fin S.count) :
    (hedgeDefectLatentExtension G defectNode).projectedBidirected i j =
      G.bidirected i j := by
  by_cases same : i = j
  · subst j
    exact (hedgeDefectLatentExtension G defectNode).projectedBidirected_irreflexive i |>.trans
      (G.bidirected_irreflexive i).symm
  · have defectFalse :
        (decide (i = defectNode) && decide (j = defectNode)) = false := by
      by_cases left : i = defectNode
      · by_cases right : j = defectNode
        · exact (same (left.trans right.symm)).elim
        · simp [left, right]
      · simp [left]
    have anyEq :
        Probability.finAny (hedgeDefectLatentCount G) (fun root =>
          hedgeDefectIncident G defectNode root i &&
            hedgeDefectIncident G defectNode root j) =
          Probability.finAny (hedgeLatentCount G) (fun root =>
            hedgeIncident G root i && hedgeIncident G root j) := by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro augmented
        rcases (Probability.finAny_eq_true_iff _).mp augmented with
          ⟨root, selected⟩
        refine Fin.cases
          (motive := fun root =>
            (hedgeDefectIncident G defectNode root i &&
                hedgeDefectIncident G defectNode root j) = true →
              Probability.finAny (hedgeLatentCount G) (fun old =>
                hedgeIncident G old i && hedgeIncident G old j) = true)
          ?_ (fun old => ?_) root selected
        · intro selected
          change (decide (i = defectNode) && decide (j = defectNode)) = true
            at selected
          rw [defectFalse] at selected
          contradiction
        · intro selected
          apply (Probability.finAny_eq_true_iff _).mpr
          change (hedgeIncident G old i && hedgeIncident G old j) = true
            at selected
          exact ⟨old, selected⟩
      · intro original
        rcases (Probability.finAny_eq_true_iff _).mp original with
          ⟨old, selected⟩
        apply (Probability.finAny_eq_true_iff _).mpr
        refine ⟨old.succ, ?_⟩
        rw [hedgeDefectIncident_succ, hedgeDefectIncident_succ]
        exact selected
    have original := hedgeLatentExtension_projected G i j
    simpa [LatentExtension.projectedBidirected, hedgeDefectLatentExtension,
      hedgeLatentExtension, anyEq] using original

/-- The augmented extension remains canonical semi-Markovian.  Old roots use
the established hedge proof, while the zero private root forces all of its
incident children to be `defectNode`. -/
theorem hedgeDefectLatentExtension_canonical (G : ObservedGraph S)
    (defectNode : Fin S.count) :
    (hedgeDefectLatentExtension G defectNode).CanonicalSemiMarkovian := by
  intro root
  refine Fin.cases
    (motive := fun root => forall i j k,
      (hedgeDefectLatentExtension G defectNode).incident root i = true ->
      (hedgeDefectLatentExtension G defectNode).incident root j = true ->
      (hedgeDefectLatentExtension G defectNode).incident root k = true ->
      i = j ∨ i = k ∨ j = k)
    ?_ (fun old => ?_) root
  · intro i j _k hi hj _hk
    change hedgeDefectIncident G defectNode (hedgeDefectRoot G) i = true at hi
    change hedgeDefectIncident G defectNode (hedgeDefectRoot G) j = true at hj
    rw [hedgeDefectIncident_zero] at hi hj
    have hi' : i = defectNode := of_decide_eq_true hi
    have hj' : j = defectNode := of_decide_eq_true hj
    exact Or.inl (hi'.trans hj'.symm)
  · intro i j k hi hj hk
    change hedgeDefectIncident G defectNode old.succ i = true at hi
    change hedgeDefectIncident G defectNode old.succ j = true at hj
    change hedgeDefectIncident G defectNode old.succ k = true at hk
    rw [hedgeDefectIncident_succ] at hi hj hk
    exact hedgeLatentExtension_canonical G old i j k
      hi hj hk

/-- Weight two for the inactive defect and weight one for the active defect.
The strict imbalance is what lets softening preserve an interventional gap;
an equiprobable XOR defect would erase it. -/
def hedgeDefectLatentWeight (G : ObservedGraph S)
    (root : Fin (hedgeDefectLatentCount G))
    (value : hedgeDefectLatentValue G root) : Nat :=
  Fin.cases
    (motive := fun root => hedgeDefectLatentValue G root → Nat)
    (fun bit => if cast (hedgeDefectLatentValue_zero G) bit then 1 else 2)
    (fun _old _value => 1)
    root value

/-- Every augmented coordinate value receives positive natural weight. -/
theorem hedgeDefectLatentWeight_pos (G : ObservedGraph S)
    (root : Fin (hedgeDefectLatentCount G))
    (value : hedgeDefectLatentValue G root) :
    0 < hedgeDefectLatentWeight G root value := by
  refine Fin.cases
    (motive := fun root => forall value : hedgeDefectLatentValue G root,
      0 < hedgeDefectLatentWeight G root value)
    ?_ (fun old => ?_) root value
  · intro bit
    simp only [hedgeDefectLatentWeight, Fin.cases_zero]
    split <;> omega
  · intro _oldValue
    simp [hedgeDefectLatentWeight]

/-- Canonical inhabitant of every augmented latent coordinate, used only to
prove that its explicit enumeration is nonempty. -/
def hedgeDefectLatentDefault (G : ObservedGraph S)
    (root : Fin (hedgeDefectLatentCount G)) :
    hedgeDefectLatentValue G root :=
  Fin.cases
    (cast (hedgeDefectLatentValue_zero G).symm false)
    (fun old => cast (hedgeDefectLatentValue_succ G old).symm
      (hedgeLatentDefault G old))
    root

/-- Positive factor on one augmented latent coordinate. -/
def hedgeDefectLatentFactor (G : ObservedGraph S)
    (root : Fin (hedgeDefectLatentCount G)) :
    FiniteProbRecord (hedgeDefectLatentValue G root) where
  atoms := (hedgeDefectLatentEnum G root).map fun value =>
    (value, hedgeDefectLatentWeight G root value)
  den := FiniteProbRecord.totalMass
    ((hedgeDefectLatentEnum G root).map fun value =>
      (value, hedgeDefectLatentWeight G root value))
  den_pos := by
    cases valuesEq : hedgeDefectLatentEnum G root with
    | nil =>
        have member := hedgeDefectLatentEnum_complete G root
          (hedgeDefectLatentDefault G root)
        rw [valuesEq] at member
        simp at member
    | cons value rest =>
        change 0 < hedgeDefectLatentWeight G root value +
          FiniteProbRecord.totalMass
            (rest.map fun entry =>
              (entry, hedgeDefectLatentWeight G root entry))
        have weightPos := hedgeDefectLatentWeight_pos G root value
        omega
  total_mass := rfl

/-- Product prior for the old hedge roots and the independent biased defect. -/
def hedgeDefectPrior (G : ObservedGraph S) :
    FiniteProbRecord ((root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :=
  FiniteProduct.record (hedgeDefectLatentCount G)
    (hedgeDefectLatentValue G) (hedgeDefectLatentFactor G)

/-- Restrict augmented latent inputs to the original hedge coordinates.
Incidence of every successor coordinate is definitionally the old incidence;
the value cast only transports across that same definitional embedding. -/
def hedgeDefectOldInputs (G : ObservedGraph S)
    (defectNode child : Fin S.count)
    (inputs : (hedgeDefectLatentExtension G defectNode).Inputs child) :
    (hedgeLatentExtension G).Inputs child := by
  intro root incident
  change Fin (hedgeLatentCount G) at root
  exact cast (hedgeDefectLatentValue_succ G root)
    (inputs root.succ (by
      have oldIncident : hedgeIncident G root child = true := by
        simpa [hedgeLatentExtension] using incident
      change hedgeDefectIncident G defectNode root.succ child = true
      rw [hedgeDefectIncident_succ]
      exact oldIncident))

/-- Read the prefixed Boolean at its unique observed child and return zero at
every other child.  The dependent incidence proof is available exactly in the
equal branch, so no default latent value or choice operation is needed. -/
def hedgeIndependentDefectBit (G : ObservedGraph S)
    (defectNode child : Fin S.count)
    (inputs : (hedgeDefectLatentExtension G defectNode).Inputs child) : Bool :=
  if equal : child = defectNode then
    cast (hedgeDefectLatentValue_zero G)
      (inputs (hedgeDefectRoot G) (by
        simpa [hedgeDefectLatentExtension] using equal))
  else false

/-- Full-alphabet softening of an old hedge mechanism.

The old mechanism still computes the structural parity bit.  An independent
biased defect flips that bit only at `defectNode`; the old private coordinate
then supplies a background label through `hedgeParityCarrierValue`.  Hence
downstream nodes see exactly the softened bit, while the mechanism can emit
arbitrary non-`second` labels rather than only `first` and `second`. -/
def hedgeCarrierDefectModel (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (defectNode : Fin S.count)
    (baseMechanism : forall child, S.ParentValues child →
      (hedgeLatentExtension G).Inputs child → S.Value child) : ExactModel S where
  latent := hedgeDefectLatentExtension G defectNode
  factor := hedgeDefectLatentFactor G
  prior := hedgeDefectPrior G
  product_law := fun events => by
    simpa [LatentExtension.rectangularEvent, hedgeDefectPrior,
      hedgeDefectLatentExtension] using
      FiniteProduct.record_rectangular_probVal
        (hedgeDefectLatentCount G) (hedgeDefectLatentValue G)
        (hedgeDefectLatentFactor G) events
  mechanism := fun child parents inputs =>
    let oldInputs := hedgeDefectOldInputs G defectNode child inputs
    let structuralBit :=
      hedgeIsSecond rich child (baseMechanism child parents oldInputs)
    let softenedBit := Bool.xor structuralBit
      (hedgeIndependentDefectBit G defectNode child inputs)
    hedgeParityCarrierValue rich child softenedBit
      (hedgePrivateDecode S child (hedgePrivateIndex G child oldInputs))

/-- The carrier wrapper preserves the observed graph because its augmented
latent source is private and all old incidence is unchanged. -/
theorem hedgeCarrierDefectModel_compatible
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (defectNode : Fin S.count)
    (baseMechanism : forall child, S.ParentValues child →
      (hedgeLatentExtension G).Inputs child → S.Value child) :
    Compatible (hedgeCarrierDefectModel G rich defectNode baseMechanism) G :=
  ⟨hedgeDefectLatentExtension_canonical G defectNode, fun i j => by
    simpa [FiniteLatentSCM.observedGraph, LatentExtension.observedGraph,
      hedgeCarrierDefectModel] using
        hedgeDefectLatentExtension_projected G defectNode i j⟩

/-- At every free node the wrapper's distinguished output bit is the old
mechanism bit XOR the independent defect.  The background label disappears
from this equation by the carrier inverse law. -/
theorem hedgeCarrierDefectModel_evalNodeUnder_bit
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (defectNode : Fin S.count)
    (baseMechanism : forall child, S.ParentValues child →
      (hedgeLatentExtension G).Inputs child → S.Value child)
    (intervention : (i : Fin S.count) → Option (S.Value i))
    (u : (hedgeDefectLatentExtension G defectNode).Assignment)
    (child : Fin S.count) (free : intervention child = none) :
    let model := hedgeCarrierDefectModel G rich defectNode baseMechanism
    let oldInputs := hedgeDefectOldInputs G defectNode child
      (fun root _incident => u root)
    hedgeIsSecond rich child (model.evalNodeUnder intervention u child) =
      Bool.xor
        (hedgeIsSecond rich child
          (baseMechanism child
            (fun parent _edge => model.evalNodeUnder intervention u parent)
            oldInputs))
        (hedgeIndependentDefectBit G defectNode child
          (fun root _incident => u root)) := by
  dsimp only
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [free]
  exact hedgeIsSecond_parityCarrierValue rich child _ _

/-- Prefix a concrete defect bit to an old hedge-latent assignment. -/
def hedgeDefectAssignment (G : ObservedGraph S)
    (old : (hedgeLatentExtension G).Assignment) (defect : Bool) :
    (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root :=
  Fin.cases
    (cast (hedgeDefectLatentValue_zero G).symm defect)
    (fun root => cast (hedgeDefectLatentValue_succ G root).symm (old root))

@[simp] theorem hedgeDefectAssignment_zero (G : ObservedGraph S)
    (old : (hedgeLatentExtension G).Assignment) (defect : Bool) :
    cast (hedgeDefectLatentValue_zero G)
        (hedgeDefectAssignment G old defect
          (hedgeDefectRoot G)) =
      defect := by
  simp [hedgeDefectAssignment, hedgeDefectRoot, hedgeDefectLatentCount]

@[simp] theorem hedgeDefectAssignment_succ (G : ObservedGraph S)
    (old : (hedgeLatentExtension G).Assignment) (defect : Bool)
    (root : Fin (hedgeLatentCount G)) :
    cast (hedgeDefectLatentValue_succ G root)
        (hedgeDefectAssignment G old defect root.succ) =
      old root := by
  simp [hedgeDefectAssignment]

/-- Projecting a prefixed assignment recovers all old latent inputs exactly. -/
theorem hedgeDefectOldInputs_assignment (G : ObservedGraph S)
    (defectNode child : Fin S.count)
    (old : (hedgeLatentExtension G).Assignment) (defect : Bool) :
    hedgeDefectOldInputs G defectNode child
        (fun root _incident => hedgeDefectAssignment G old defect root) =
      (fun root _incident => old root) := by
  funext root incident
  change Fin (hedgeLatentCount G) at root
  exact hedgeDefectAssignment_succ G old defect root

/-- The prefixed assignment exposes its defect at the selected child. -/
theorem hedgeIndependentDefectBit_assignment_same (G : ObservedGraph S)
    (defectNode : Fin S.count)
    (old : (hedgeLatentExtension G).Assignment) (defect : Bool) :
    hedgeIndependentDefectBit G defectNode defectNode
        (fun root _incident => hedgeDefectAssignment G old defect root) =
      defect := by
  simp [hedgeIndependentDefectBit, hedgeDefectAssignment,
    hedgeDefectRoot, hedgeDefectLatentCount]

/-- The same prefixed coordinate is inaccessible at every other child. -/
theorem hedgeIndependentDefectBit_assignment_other (G : ObservedGraph S)
    (defectNode child : Fin S.count) (different : child ≠ defectNode)
    (old : (hedgeLatentExtension G).Assignment) (defect : Bool) :
    hedgeIndependentDefectBit G defectNode child
        (fun root _incident => hedgeDefectAssignment G old defect root) =
      false := by
  simp [hedgeIndependentDefectBit, different]

/-- Old hedge assignment with prescribed pair-root bits and private
background coordinates decoding to `target`.  Unlike
`hedgeSupportLatentWithPairs`, no parent or pair toggle is folded into the
private coordinate: the carrier mechanism needs the target label itself. -/
def hedgeCarrierSupportLatent (G : ObservedGraph S) (target : S.Assignment)
    (pairBits : Fin (pairRootCount G) → Bool) :
    (hedgeLatentExtension G).Assignment :=
  hedgeLatentOfCoordinates G pairBits
    (fun child => hedgeIndexOfValue S child (target child))

/-- Pair-root recovery from the carrier support is exact. -/
theorem hedgePairBitsOf_carrierSupportLatent (G : ObservedGraph S)
    (target : S.Assignment)
    (pairBits : Fin (pairRootCount G) → Bool) :
    hedgePairBitsOf G (hedgeCarrierSupportLatent G target pairBits) = pairBits :=
  hedgePairBitsOf_latentOfCoordinates G pairBits
    (fun child => hedgeIndexOfValue S child (target child))

/-- The private background at every node decodes to the requested observed
value. -/
theorem hedgeCarrierSupportLatent_privateDecode (G : ObservedGraph S)
    (target : S.Assignment)
    (pairBits : Fin (pairRootCount G) → Bool) (child : Fin S.count) :
    hedgePrivateDecode S child
        (hedgePrivateIndex G child (fun root _incident =>
          hedgeCarrierSupportLatent G target pairBits root)) =
      target child := by
  have coordinates := congrFun
    (hedgePrivateCoordinatesOf_latentOfCoordinates G pairBits
      (fun node => hedgeIndexOfValue S node (target node))) child
  change hedgePrivateIndex G child (fun root _incident =>
    hedgeCarrierSupportLatent G target pairBits root) =
      hedgeIndexOfValue S child (target child) at coordinates
  rw [coordinates, hedgePrivateDecode_index]

/-- Full-alphabet large-forest parity model with its independent defect at
the common root selected from the hedge witness. -/
def HedgeWitness.largeCarrierDefectParityModel
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ExactModel S :=
  hedgeCarrierDefectModel G rich w.actionRoot
    (w.largeParityModel rich).mechanism

/-- Full-alphabet nested small-forest model with the same defect coordinate,
factor weights, and background-label carrier. -/
def HedgeWitness.smallCarrierDefectParityModel
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ExactModel S :=
  hedgeCarrierDefectModel G rich w.actionRoot
    (w.smallParityModel rich).mechanism

/-- The augmented large model is compatible with the original ADMG. -/
theorem HedgeWitness.largeCarrierDefectParityModel_compatible
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Compatible (w.largeCarrierDefectParityModel rich) G :=
  hedgeCarrierDefectModel_compatible G rich w.actionRoot
    (w.largeParityModel rich).mechanism

/-- The augmented small model is compatible with the original ADMG. -/
theorem HedgeWitness.smallCarrierDefectParityModel_compatible
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    Compatible (w.smallCarrierDefectParityModel rich) G :=
  hedgeCarrierDefectModel_compatible G rich w.actionRoot
    (w.smallParityModel rich).mechanism

/-- Both augmented models use definitionally the same product prior. -/
theorem HedgeWitness.carrierDefectParityModel_prior_eq
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    (w.largeCarrierDefectParityModel rich).prior =
      (w.smallCarrierDefectParityModel rich).prior :=
  rfl

/-- A listed value with positive weight has positive singleton mass in the
corresponding weighted atom list.  Duplicates, if present, only add further
nonnegative mass, so no uniqueness hypothesis is required. -/
theorem eventMass_weighted_singleton_pos
    {Ω : Type _} [DecidableEq Ω]
    (values : List Ω) (weight : Ω → Nat)
    (weightPos : forall value, 0 < weight value)
    (chosen : Ω) (member : chosen ∈ values) :
    0 < FiniteProbRecord.eventMass
      (values.map fun value => (value, weight value))
      (FiniteProbRecord.singletonEvent chosen) := by
  induction values with
  | nil => cases member
  | cons value rest inductionHypothesis =>
      cases List.mem_cons.mp member with
      | inl equal =>
          subst value
          simp only [List.map_cons, FiniteProbRecord.eventMass,
            FiniteProbRecord.singletonEvent, decide_true, if_true]
          have chosenPos := weightPos chosen
          omega
      | inr inRest =>
          by_cases equal : value = chosen
          · subst value
            simp only [List.map_cons, FiniteProbRecord.eventMass,
              FiniteProbRecord.singletonEvent, decide_true, if_true]
            have chosenPos := weightPos chosen
            omega
          · have tailPos := inductionHypothesis inRest
            simpa [FiniteProbRecord.eventMass,
              FiniteProbRecord.singletonEvent, equal] using tailPos

/-- Every enumerated value has positive singleton mass in its augmented
factor. -/
theorem hedgeDefectLatentFactor_singleton_mass_pos
    (G : ObservedGraph S) (root : Fin (hedgeDefectLatentCount G))
    (value : hedgeDefectLatentValue G root) :
    0 < FiniteProbRecord.eventMass (hedgeDefectLatentFactor G root).atoms
      (FiniteProbRecord.singletonEvent value) := by
  exact eventMass_weighted_singleton_pos
    (hedgeDefectLatentEnum G root) (hedgeDefectLatentWeight G root)
    (hedgeDefectLatentWeight_pos G root) value
    (hedgeDefectLatentEnum_complete G root value)

/-- Coordinate singletons form exactly the singleton event on an augmented
latent assignment. -/
theorem hedgeDefectRectangular_eq_singleton (G : ObservedGraph S)
    (u : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :
    FiniteProduct.rectangularEvent (hedgeDefectLatentCount G)
        (hedgeDefectLatentValue G)
        (fun root value => decide (value = u root)) =
      FiniteProbRecord.singletonEvent u := by
  funext assignment
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro rectangular
    have pointwise :=
      (FiniteProduct.rectangularEvent_eq_true_iff
        (hedgeDefectLatentCount G) (hedgeDefectLatentValue G)
        (fun root value => decide (value = u root)) assignment).mp rectangular
    have equal : assignment = u :=
      funext fun root => of_decide_eq_true (pointwise root)
    simp [FiniteProbRecord.singletonEvent, equal]
  · intro singleton
    have equal : assignment = u := of_decide_eq_true (by
      simpa [FiniteProbRecord.singletonEvent] using singleton)
    exact
      (FiniteProduct.rectangularEvent_eq_true_iff
        (hedgeDefectLatentCount G) (hedgeDefectLatentValue G)
        (fun root value => decide (value = u root)) assignment).mpr
          (fun root => by simp [equal])

/-- Every complete augmented latent assignment has positive mass under the
biased product prior. -/
theorem hedgeDefectPrior_singleton_mass_pos (G : ObservedGraph S)
    (u : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :
    0 < FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
      (FiniteProbRecord.singletonEvent u) := by
  rw [← hedgeDefectRectangular_eq_singleton G u]
  change 0 < FiniteProbRecord.eventMass
    (FiniteProduct.atoms (hedgeDefectLatentCount G)
      (hedgeDefectLatentValue G) (hedgeDefectLatentFactor G))
    (FiniteProduct.rectangularEvent (hedgeDefectLatentCount G)
      (hedgeDefectLatentValue G)
      (fun root value => decide (value = u root)))
  rw [FiniteProduct.eventMass_atoms]
  apply natProduct_pos
  intro root
  simpa [FiniteProbRecord.singletonEvent] using
    hedgeDefectLatentFactor_singleton_mass_pos G root (u root)

/-- A finite SCM is observationally positive when every latent atom has
positive prior mass and every observed assignment has an explicit evaluation
preimage.

Both hypotheses live in `Prop`; eliminating the preimage existential therefore
does not choose data for a definition.  Concrete hedge models below supply an
actual preimage function anyway, but this semantic packaging keeps the mass
argument independent of that construction. -/
theorem FiniteLatentSCM.observationallyPositive_of_eval_surjective
    (model : ExactModel S)
    (priorPositive : forall u : model.latent.Assignment,
      0 < FiniteProbRecord.eventMass model.prior.atoms
        (FiniteProbRecord.singletonEvent u))
    (surjective : forall target : S.Assignment,
      Exists fun u : model.latent.Assignment => model.eval u = target) :
    ObservationallyPositive model := by
  intro target
  rcases surjective target with ⟨preimage, evaluates⟩
  have subset : forall u,
      FiniteProbRecord.singletonEvent preimage u = true ->
        FiniteProbRecord.singletonEvent target (model.eval u) = true := by
    intro u singleton
    have equal : u = preimage := of_decide_eq_true (by
      simpa [FiniteProbRecord.singletonEvent] using singleton)
    subst u
    simp [FiniteProbRecord.singletonEvent, evaluates]
  have monotone := FiniteProbRecord.eventMass_mono model.prior.atoms
    (FiniteProbRecord.singletonEvent preimage)
    (fun u => FiniteProbRecord.singletonEvent target (model.eval u)) subset
  have positiveEvent :
      0 < FiniteProbRecord.eventMass model.prior.atoms
        (fun u => FiniteProbRecord.singletonEvent target (model.eval u)) :=
    Nat.lt_of_lt_of_le (priorPositive preimage) monotone
  simpa [FiniteLatentSCM.observationalDist, FiniteProbRecord.probVal,
    FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels] using
      positiveEvent

/-!
### Normalizing an arbitrary incidence target with one defect

Incidence generated by pair roots has even parity on a bidirected component.
The prefixed private root removes that restriction: its bit is chosen as the
parity of the requested incidence and is injected at one selected anchor.
After that single correction the remaining pair-root target is even and can
be recovered by the existing exhaustive component section.
-/

/-- Correct a Boolean incidence target at one anchor by its total selected
parity. -/
def hedgeDefectAdjustedTarget (nodes : NodeSet S) (anchor : Fin S.count)
    (target : Fin S.count → Bool) (node : Fin S.count) : Bool :=
  Bool.xor (target node)
    (if node = anchor then hedgeNodeXor nodes target else false)

/-- XOR of a one-anchor vector is its selected bit. -/
theorem hedgeNodeXor_singleAnchor (nodes : NodeSet S)
    (anchor : Fin S.count) (inside : nodes anchor = true) (bit : Bool) :
    hedgeNodeXor nodes (fun node => if node = anchor then bit else false) =
      bit := by
  unfold hedgeNodeXor
  cases bit with
  | false =>
      exact foldl_unchanged _ false (NodeSet.members nodes)
        (fun total node => by simp)
  | true =>
      have member := (NodeSet.mem_members_iff nodes anchor).mpr inside
      simpa using foldl_xor_indicator_of_mem_nodup
        (NodeSet.members nodes) anchor member (NodeSet.nodup_members nodes)

/-- The anchor correction has even support, stated in the exact list-parity
form consumed by `BidirectedComponent.evenTargetPairBits`. -/
theorem hedgeDefectAdjustedTarget_even (nodes : NodeSet S)
    (anchor : Fin S.count) (inside : nodes anchor = true)
    (target : Fin S.count → Bool) :
    (hedgeTrueVertices nodes
      (hedgeDefectAdjustedTarget nodes anchor target)).length % 2 = 0 := by
  apply (foldl_xor_eq_false_iff_filter_even
    (hedgeDefectAdjustedTarget nodes anchor target)
    (NodeSet.members nodes)).mp
  unfold hedgeDefectAdjustedTarget
  rw [foldl_xor_pointwise]
  change Bool.xor (hedgeNodeXor nodes target)
      (hedgeNodeXor nodes (fun node =>
        if node = anchor then hedgeNodeXor nodes target else false)) = false
  rw [hedgeNodeXor_singleAnchor nodes anchor inside (hedgeNodeXor nodes target)]
  generalize hedgeNodeXor nodes target = parity
  cases parity <;> rfl

/-- Incidence demanded by a large-forest target after correcting its parity at
the witness's common action root. -/
def HedgeWitness.largeCarrierDefectIncidence
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) : Fin S.count → Bool :=
  hedgeDefectAdjustedTarget w.large w.actionRoot
    (hedgeForestRequiredIncidence rich w.child target)

/-- The independent defect bit required by a large observed target. -/
def HedgeWitness.largeCarrierDefectBit
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) : Bool :=
  hedgeNodeXor w.large (hedgeForestRequiredIncidence rich w.child target)

/-- The corrected large incidence is admissible for pair-root realization. -/
theorem HedgeWitness.largeCarrierDefectIncidence_even
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (hedgeTrueVertices w.large
      (w.largeCarrierDefectIncidence rich target)).length % 2 = 0 :=
  hedgeDefectAdjustedTarget_even w.large w.actionRoot w.actionRoot_in_large
    (hedgeForestRequiredIncidence rich w.child target)

/-- Canonical pair-root assignment realizing the corrected large incidence. -/
def HedgeWitness.largeCarrierDefectPairBits
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) : Fin (pairRootCount G) → Bool :=
  w.large_forest.component.evenTargetPairBits G w.large
    (w.largeCarrierDefectIncidence rich target)
    (w.largeCarrierDefectIncidence_even rich target)

/-- The canonical large pair-root assignment satisfies the corrected target
at every large-forest vertex. -/
theorem HedgeWitness.largeCarrierDefectPairBits_spec
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) (node : Fin S.count)
    (inside : w.large node = true) :
    hedgeXorPairBitsWithinFrom G w.large node
        (w.largeCarrierDefectPairBits rich target) =
      w.largeCarrierDefectIncidence rich target node :=
  w.large_forest.component.evenTargetPairBits_spec G w.large
    (w.largeCarrierDefectIncidence rich target)
    (w.largeCarrierDefectIncidence_even rich target) node inside

/-- Nested incidence demanded by a small-model target after correcting the
inner component parity at the same common root. -/
def HedgeWitness.smallCarrierDefectIncidence
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) : Fin S.count → Bool :=
  hedgeDefectAdjustedTarget w.small w.actionRoot
    (hedgeNestedForestRequiredIncidence rich w.small w.child
      (restrictChild w.small w.child) target)

/-- The independent defect bit required by the inner small component. -/
def HedgeWitness.smallCarrierDefectBit
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) : Bool :=
  hedgeNodeXor w.small
    (hedgeNestedForestRequiredIncidence rich w.small w.child
      (restrictChild w.small w.child) target)

/-- On the selected small component, the nested incidence function always
takes its inner branch.  This puts the defect parity in the same normal form
as the small structural equation. -/
theorem HedgeWitness.smallCarrierDefectBit_eq_inner
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    w.smallCarrierDefectBit rich target =
      hedgeNodeXor w.small
        (hedgeForestRequiredIncidence rich
          (restrictChild w.small w.child) target) := by
  unfold HedgeWitness.smallCarrierDefectBit hedgeNodeXor
  apply foldl_congr_of_mem
  intro total node member
  have selected := (NodeSet.mem_members_iff w.small node).mp member
  simp [hedgeNestedForestRequiredIncidence, selected]

/-- Corrected small incidence has even support on the inner component. -/
theorem HedgeWitness.smallCarrierDefectIncidence_even
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (hedgeTrueVertices w.small
      (w.smallCarrierDefectIncidence rich target)).length % 2 = 0 :=
  hedgeDefectAdjustedTarget_even w.small w.actionRoot w.actionRoot_in_small
    (hedgeNestedForestRequiredIncidence rich w.small w.child
      (restrictChild w.small w.child) target)

/-- Canonical pair-root assignment realizing the complete corrected nested
incidence: arbitrary on `large \ small`, even on `small`. -/
def HedgeWitness.smallCarrierDefectPairBits
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) : Fin (pairRootCount G) → Bool :=
  w.large_forest.component.nestedEvenTargetPairBits G w.large w.small
    w.small_forest.component w.small_subset_large
    (w.smallCarrierDefectIncidence rich target)
    (w.smallCarrierDefectIncidence_even rich target)

/-- The canonical nested assignment satisfies the corrected target at every
large-forest vertex. -/
theorem HedgeWitness.smallCarrierDefectPairBits_spec
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) (node : Fin S.count)
    (inside : w.large node = true) :
    hedgeNestedXorPairBitsWithinFrom G w.large w.small node
        (w.smallCarrierDefectPairBits rich target) =
      w.smallCarrierDefectIncidence rich target node :=
  w.large_forest.component.nestedEvenTargetPairBits_spec G w.large w.small
    w.small_forest.component w.small_subset_large
    (w.smallCarrierDefectIncidence rich target)
    (w.smallCarrierDefectIncidence_even rich target) node inside

/-- Concrete augmented latent preimage proposed for an arbitrary target in
the large carrier model. -/
def HedgeWitness.largeCarrierDefectSupportLatent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (hedgeDefectLatentExtension G w.actionRoot).Assignment :=
  hedgeDefectAssignment G
    (hedgeCarrierSupportLatent G target
      (w.largeCarrierDefectPairBits rich target))
    (w.largeCarrierDefectBit rich target)

/-- Concrete augmented latent preimage proposed for the nested small model. -/
def HedgeWitness.smallCarrierDefectSupportLatent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (hedgeDefectLatentExtension G w.actionRoot).Assignment :=
  hedgeDefectAssignment G
    (hedgeCarrierSupportLatent G target
      (w.smallCarrierDefectPairBits rich target))
    (w.smallCarrierDefectBit rich target)

/-- The canonical large support assignment evaluates to its requested target.
The proof follows the observed topological order.  Parent outputs are already
the target by induction; the corrected pair incidence then supplies the
required structural bit, and the independent defect restores the original
target bit at the common root. -/
theorem HedgeWitness.largeCarrierDefectParityModel_evalNode_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) (child : Fin S.count) :
    (w.largeCarrierDefectParityModel rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S)
        (w.largeCarrierDefectSupportLatent rich target) child =
      target child := by
  let pairBits := w.largeCarrierDefectPairBits rich target
  let oldSupport := hedgeCarrierSupportLatent G target pairBits
  let defect := w.largeCarrierDefectBit rich target
  let support := hedgeDefectAssignment G oldSupport defect
  have supportEq :
      w.largeCarrierDefectSupportLatent rich target = support := by
    rfl
  have oldInputsEq :
      hedgeDefectOldInputs G w.actionRoot child
          (fun root _incident => support root) =
        (fun root _incident => oldSupport root) := by
    exact hedgeDefectOldInputs_assignment G w.actionRoot child
      oldSupport defect
  have background :
      hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun root _incident => oldSupport root)) =
        target child := by
    exact hedgeCarrierSupportLatent_privateDecode G target pairBits child
  have defectAt :
      hedgeIndependentDefectBit G w.actionRoot child
          (fun root _incident => support root) =
        if child = w.actionRoot then defect else false := by
    by_cases equal : child = w.actionRoot
    · subst child
      simpa using hedgeIndependentDefectBit_assignment_same G w.actionRoot
        oldSupport defect
    · simpa [equal] using hedgeIndependentDefectBit_assignment_other G
        w.actionRoot child equal oldSupport defect
  rw [supportEq]
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  simp only [HedgeWitness.largeCarrierDefectParityModel,
    hedgeCarrierDefectModel]
  rw [oldInputsEq, background, defectAt]
  refine (congrArg
    (fun bit => hedgeParityCarrierValue rich child bit (target child)) ?_).trans
      (hedgeParityCarrierValue_reconstruct rich child (target child))
  change Bool.xor
      (hedgeIsSecond rich child
        ((w.largeParityModel rich).mechanism child
          (fun parent _edge =>
            (w.largeCarrierDefectParityModel rich).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) support parent)
          (fun root _incident => oldSupport root)))
      (if child = w.actionRoot then defect else false) =
    hedgeIsSecond rich child (target child)
  cases inside : w.large child with
  | false =>
      have different : child ≠ w.actionRoot := by
        intro equal
        subst child
        rw [w.actionRoot_in_large] at inside
        contradiction
      have baseOutside :
          hedgeIsSecond rich child
              ((w.largeParityModel rich).mechanism child
                (fun parent _edge =>
                  (w.largeCarrierDefectParityModel rich).evalNodeUnder
                    (FiniteLatentSCM.noIntervention S) support parent)
                (fun root _incident => oldSupport root)) =
            hedgeIsSecond rich child (target child) := by
        simp [HedgeWitness.largeParityModel, hedgeForestParityModel,
          hedgeForestParityOutput, inside, background]
      rw [baseOutside]
      simp [different]
  | true =>
      have parentsEq :
          hedgeForestParentBitsFrom rich w.child child
              (fun parent edge =>
                (w.largeCarrierDefectParityModel rich).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) support parent) =
            hedgeForestParentBitsFrom rich w.child child
              (fun parent _edge => target parent) := by
        exact hedgeForestParentBitsFrom_congr rich child
          (fun _parent => rfl)
          (fun parent edge =>
            w.largeCarrierDefectParityModel_evalNode_support rich target parent)
      have pairEq :
          hedgeXorPairBitsWithin G w.large child
              (fun root _incident => oldSupport root) =
            w.largeCarrierDefectIncidence rich target child := by
        rw [hedgeXorPairBitsWithin_pairBitsOf,
          hedgePairBitsOf_carrierSupportLatent]
        exact w.largeCarrierDefectPairBits_spec rich target child inside
      have baseBit := hedgeForestParityOutput_bit_of_mem G rich w.large
        w.child child
        (fun parent edge =>
          (w.largeCarrierDefectParityModel rich).evalNodeUnder
            (FiniteLatentSCM.noIntervention S) support parent)
        (fun root _incident => oldSupport root) inside
      change hedgeIsSecond rich child
          ((w.largeParityModel rich).mechanism child
            (fun parent edge =>
              (w.largeCarrierDefectParityModel rich).evalNodeUnder
                (FiniteLatentSCM.noIntervention S) support parent)
            (fun root _incident => oldSupport root)) = _ at baseBit
      rw [baseBit, pairEq, parentsEq]
      dsimp only [defect]
      unfold HedgeWitness.largeCarrierDefectIncidence
        hedgeDefectAdjustedTarget HedgeWitness.largeCarrierDefectBit
        hedgeForestRequiredIncidence
      by_cases equal : child = w.actionRoot <;> simp only [equal, if_true,
        if_false]
      all_goals
        generalize hedgeIsSecond rich child (target child) = output
        generalize hedgeForestParentBitsFrom rich w.child child
          (fun parent _edge => target parent) = parents
        generalize hedgeNodeXor w.large (fun node =>
          Bool.xor (hedgeIsSecond rich node (target node))
            (hedgeForestParentBitsFrom rich w.child node
              (fun parent _edge => target parent))) = parity
        cases output <;> cases parents <;> cases parity <;> rfl
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

/-- Evaluation of the large carrier model is surjective onto complete
observed assignments. -/
theorem HedgeWitness.largeCarrierDefectParityModel_eval_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (w.largeCarrierDefectParityModel rich).eval
        (w.largeCarrierDefectSupportLatent rich target) = target := by
  funext child
  exact w.largeCarrierDefectParityModel_evalNode_support rich target child

/-- The full-alphabet large carrier has strictly positive observational mass
at every assignment. -/
theorem HedgeWitness.largeCarrierDefectParityModel_positive
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ObservationallyPositive (w.largeCarrierDefectParityModel rich) := by
  apply FiniteLatentSCM.observationallyPositive_of_eval_surjective
  · intro u
    simpa [HedgeWitness.largeCarrierDefectParityModel,
      hedgeCarrierDefectModel] using hedgeDefectPrior_singleton_mass_pos G u
  · intro target
    exact ⟨w.largeCarrierDefectSupportLatent rich target,
      w.largeCarrierDefectParityModel_eval_support rich target⟩

/-- The canonical nested support assignment evaluates to its requested
target.  Outside `large` the private background is returned directly; on
`large \ small` the outer forest equation is used; on `small` the restricted
inner equation is used.  The same defect algebra closes both selected cases. -/
theorem HedgeWitness.smallCarrierDefectParityModel_evalNode_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) (child : Fin S.count) :
    (w.smallCarrierDefectParityModel rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S)
        (w.smallCarrierDefectSupportLatent rich target) child =
      target child := by
  let pairBits := w.smallCarrierDefectPairBits rich target
  let oldSupport := hedgeCarrierSupportLatent G target pairBits
  let defect := w.smallCarrierDefectBit rich target
  let support := hedgeDefectAssignment G oldSupport defect
  have supportEq :
      w.smallCarrierDefectSupportLatent rich target = support := by
    rfl
  have oldInputsEq :
      hedgeDefectOldInputs G w.actionRoot child
          (fun root _incident => support root) =
        (fun root _incident => oldSupport root) :=
    hedgeDefectOldInputs_assignment G w.actionRoot child oldSupport defect
  have background :
      hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun root _incident => oldSupport root)) =
        target child :=
    hedgeCarrierSupportLatent_privateDecode G target pairBits child
  have defectAt :
      hedgeIndependentDefectBit G w.actionRoot child
          (fun root _incident => support root) =
        if child = w.actionRoot then defect else false := by
    by_cases equal : child = w.actionRoot
    · subst child
      simpa using hedgeIndependentDefectBit_assignment_same G w.actionRoot
        oldSupport defect
    · simpa [equal] using hedgeIndependentDefectBit_assignment_other G
        w.actionRoot child equal oldSupport defect
  rw [supportEq]
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  simp only [HedgeWitness.smallCarrierDefectParityModel,
    hedgeCarrierDefectModel]
  rw [oldInputsEq, background, defectAt]
  refine (congrArg
    (fun bit => hedgeParityCarrierValue rich child bit (target child)) ?_).trans
      (hedgeParityCarrierValue_reconstruct rich child (target child))
  change Bool.xor
      (hedgeIsSecond rich child
        ((w.smallParityModel rich).mechanism child
          (fun parent _edge =>
            (w.smallCarrierDefectParityModel rich).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) support parent)
          (fun root _incident => oldSupport root)))
      (if child = w.actionRoot then defect else false) =
    hedgeIsSecond rich child (target child)
  cases inLarge : w.large child with
  | false =>
      have inSmall : w.small child = false := by
        cases selected : w.small child
        · rfl
        · have selectedLarge := w.small_subset_large child selected
          rw [inLarge] at selectedLarge
          contradiction
      have different : child ≠ w.actionRoot := by
        intro equal
        subst child
        rw [w.actionRoot_in_large] at inLarge
        contradiction
      have baseOutside :
          hedgeIsSecond rich child
              ((w.smallParityModel rich).mechanism child
                (fun parent _edge =>
                  (w.smallCarrierDefectParityModel rich).evalNodeUnder
                    (FiniteLatentSCM.noIntervention S) support parent)
                (fun root _incident => oldSupport root)) =
            hedgeIsSecond rich child (target child) := by
        simp [HedgeWitness.smallParityModel, hedgeNestedForestParityModel,
          hedgeForestParityOutput, inSmall, inLarge, background]
      rw [baseOutside]
      simp [different]
  | true =>
      cases inSmall : w.small child with
      | false =>
          have parentsEq :
              hedgeForestParentBitsFrom rich w.child child
                  (fun parent edge =>
                    (w.smallCarrierDefectParityModel rich).evalNodeUnder
                      (FiniteLatentSCM.noIntervention S) support parent) =
                hedgeForestParentBitsFrom rich w.child child
                  (fun parent _edge => target parent) := by
            exact hedgeForestParentBitsFrom_congr rich child
              (fun _parent => rfl)
              (fun parent edge =>
                w.smallCarrierDefectParityModel_evalNode_support rich target
                  parent)
          have pairEq :
              hedgeXorPairBitsWithin G w.large child
                  (fun root _incident => oldSupport root) =
                w.smallCarrierDefectIncidence rich target child := by
            rw [hedgeXorPairBitsWithin_pairBitsOf,
              hedgePairBitsOf_carrierSupportLatent]
            simpa [hedgeNestedXorPairBitsWithinFrom, inSmall] using
              w.smallCarrierDefectPairBits_spec rich target child inLarge
          have baseBit := hedgeForestParityOutput_bit_of_mem G rich w.large
            w.child child
            (fun parent edge =>
              (w.smallCarrierDefectParityModel rich).evalNodeUnder
                (FiniteLatentSCM.noIntervention S) support parent)
            (fun root _incident => oldSupport root) inLarge
          have smallBaseBit : hedgeIsSecond rich child
              ((w.smallParityModel rich).mechanism child
                (fun parent edge =>
                  (w.smallCarrierDefectParityModel rich).evalNodeUnder
                    (FiniteLatentSCM.noIntervention S) support parent)
                (fun root _incident => oldSupport root)) =
              Bool.xor
                (hedgeXorPairBitsWithin G w.large child
                  (fun root _incident => oldSupport root))
                (hedgeForestParentBitsFrom rich w.child child
                  (fun parent edge =>
                    (w.smallCarrierDefectParityModel rich).evalNodeUnder
                      (FiniteLatentSCM.noIntervention S) support parent)) := by
            rw [← w.parityMechanism_eq_of_not_small rich child _ _ inSmall]
            exact baseBit
          have structuralEq :
              Bool.xor
                  (hedgeXorPairBitsWithin G w.large child
                    (fun root _incident => oldSupport root))
                  (hedgeForestParentBitsFrom rich w.child child
                    (fun parent edge =>
                      (w.smallCarrierDefectParityModel rich).evalNodeUnder
                        (FiniteLatentSCM.noIntervention S) support parent)) =
                Bool.xor (w.smallCarrierDefectIncidence rich target child)
                  (hedgeForestParentBitsFrom rich w.child child
                    (fun parent _edge => target parent)) := by
            rw [pairEq, parentsEq]
          rw [smallBaseBit, structuralEq]
          dsimp only [defect]
          unfold HedgeWitness.smallCarrierDefectIncidence
            hedgeDefectAdjustedTarget HedgeWitness.smallCarrierDefectBit
            hedgeNestedForestRequiredIncidence hedgeForestRequiredIncidence
          simp only [inSmall, Bool.false_eq_true, if_false]
          have different : child ≠ w.actionRoot := by
            intro equal
            subst child
            rw [w.actionRoot_in_small] at inSmall
            contradiction
          simp only [different, if_false]
          generalize hedgeIsSecond rich child (target child) = output
          generalize hedgeForestParentBitsFrom rich w.child child
            (fun parent _edge => target parent) = parents
          cases output <;> cases parents <;> rfl
      | true =>
          let smallKept := restrictChild w.small w.child
          have parentsEq :
              hedgeForestParentBitsFrom rich smallKept child
                  (fun parent edge =>
                    (w.smallCarrierDefectParityModel rich).evalNodeUnder
                      (FiniteLatentSCM.noIntervention S) support parent) =
                hedgeForestParentBitsFrom rich smallKept child
                  (fun parent _edge => target parent) := by
            exact hedgeForestParentBitsFrom_congr rich child
              (fun _parent => rfl)
              (fun parent edge =>
                w.smallCarrierDefectParityModel_evalNode_support rich target
                  parent)
          have pairEq :
              hedgeXorPairBitsWithin G w.small child
                  (fun root _incident => oldSupport root) =
                w.smallCarrierDefectIncidence rich target child := by
            rw [hedgeXorPairBitsWithin_pairBitsOf,
              hedgePairBitsOf_carrierSupportLatent]
            simpa [hedgeNestedXorPairBitsWithinFrom, inSmall] using
              w.smallCarrierDefectPairBits_spec rich target child inLarge
          have baseBit := hedgeForestParityOutput_bit_of_mem G rich w.small
            smallKept child
            (fun parent edge =>
              (w.smallCarrierDefectParityModel rich).evalNodeUnder
                (FiniteLatentSCM.noIntervention S) support parent)
            (fun root _incident => oldSupport root) inSmall
          have smallBaseBit : hedgeIsSecond rich child
              ((w.smallParityModel rich).mechanism child
                (fun parent edge =>
                  (w.smallCarrierDefectParityModel rich).evalNodeUnder
                    (FiniteLatentSCM.noIntervention S) support parent)
                (fun root _incident => oldSupport root)) =
              Bool.xor
                (hedgeXorPairBitsWithin G w.small child
                  (fun root _incident => oldSupport root))
                (hedgeForestParentBitsFrom rich smallKept child
                  (fun parent edge =>
                    (w.smallCarrierDefectParityModel rich).evalNodeUnder
                      (FiniteLatentSCM.noIntervention S) support parent)) := by
            rw [w.smallParityMechanism_of_small rich child _ _ inSmall]
            exact baseBit
          have structuralEq :
              Bool.xor
                  (hedgeXorPairBitsWithin G w.small child
                    (fun root _incident => oldSupport root))
                  (hedgeForestParentBitsFrom rich smallKept child
                    (fun parent edge =>
                      (w.smallCarrierDefectParityModel rich).evalNodeUnder
                        (FiniteLatentSCM.noIntervention S) support parent)) =
                Bool.xor (w.smallCarrierDefectIncidence rich target child)
                  (hedgeForestParentBitsFrom rich smallKept child
                    (fun parent _edge => target parent)) := by
            rw [pairEq, parentsEq]
          rw [smallBaseBit, structuralEq]
          have nestedParityEq :
              hedgeNodeXor w.small
                  (hedgeNestedForestRequiredIncidence rich w.small w.child
                    (restrictChild w.small w.child) target) =
                hedgeNodeXor w.small
                  (hedgeForestRequiredIncidence rich
                    (restrictChild w.small w.child) target) := by
            simpa [HedgeWitness.smallCarrierDefectBit] using
              w.smallCarrierDefectBit_eq_inner rich target
          dsimp only [defect, smallKept]
          rw [w.smallCarrierDefectBit_eq_inner rich target]
          unfold HedgeWitness.smallCarrierDefectIncidence
            hedgeDefectAdjustedTarget
          rw [nestedParityEq]
          unfold hedgeNestedForestRequiredIncidence hedgeForestRequiredIncidence
          simp only [inSmall, if_true]
          by_cases equal : child = w.actionRoot <;>
            simp only [equal, if_true, if_false]
          all_goals
            generalize hedgeIsSecond rich child (target child) = output
            generalize hedgeForestParentBitsFrom rich
              (restrictChild w.small w.child) child
              (fun parent _edge => target parent) = parents
            generalize hedgeNodeXor w.small (fun node =>
              Bool.xor (hedgeIsSecond rich node (target node))
                (hedgeForestParentBitsFrom rich
                  (restrictChild w.small w.child) node
                  (fun parent _edge => target parent))) = parity
            cases output <;> cases parents <;> cases parity <;> rfl
termination_by child.val
decreasing_by
  all_goals exact S.directed_earlier edge

/-- Evaluation of the nested carrier model is also surjective. -/
theorem HedgeWitness.smallCarrierDefectParityModel_eval_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (w.smallCarrierDefectParityModel rich).eval
        (w.smallCarrierDefectSupportLatent rich target) = target := by
  funext child
  exact w.smallCarrierDefectParityModel_evalNode_support rich target child

/-- The nested full-alphabet carrier has strictly positive observational mass
at every assignment. -/
theorem HedgeWitness.smallCarrierDefectParityModel_positive
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ObservationallyPositive (w.smallCarrierDefectParityModel rich) := by
  apply FiniteLatentSCM.observationallyPositive_of_eval_surjective
  · intro u
    simpa [HedgeWitness.smallCarrierDefectParityModel,
      hedgeCarrierDefectModel] using hedgeDefectPrior_singleton_mass_pos G u
  · intro target
    exact ⟨w.smallCarrierDefectSupportLatent rich target,
      w.smallCarrierDefectParityModel_eval_support rich target⟩

/-!
### Common defect parity and pair-root fiber size

The two carrier models must use the same weighted defect value on a common
observed target.  This follows from the earlier c-forest theorem saying that
the large and nested required-incidence patterns are even simultaneously.
Once corrected, both pair-root fibers are even and the existing cross-map
kernel theorem gives equal cardinality.
-/

/-- Selected XOR is false exactly when the corresponding true-vertex list has
even length. -/
theorem hedgeNodeXor_eq_false_iff_even (nodes : NodeSet S)
    (bits : Fin S.count → Bool) :
    hedgeNodeXor nodes bits = false ↔
      (hedgeTrueVertices nodes bits).length % 2 = 0 := by
  simpa [hedgeNodeXor, hedgeTrueVertices] using
    foldl_xor_eq_false_iff_filter_even bits (NodeSet.members nodes)

/-- Large and small targets select the same independent defect bit. -/
theorem HedgeWitness.largeCarrierDefectBit_eq_small
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    w.largeCarrierDefectBit rich target =
      w.smallCarrierDefectBit rich target := by
  let largeRequired := hedgeForestRequiredIncidence rich w.child target
  let smallRequired := hedgeNestedForestRequiredIncidence rich w.small w.child
    (restrictChild w.small w.child) target
  have parityIff :
      (hedgeTrueVertices w.large largeRequired).length % 2 = 0 ↔
        (hedgeTrueVertices w.small smallRequired).length % 2 = 0 := by
    simpa [largeRequired, smallRequired] using
      w.largeRequiredEven_iff_smallRequiredEven rich target
  cases largeParity : hedgeNodeXor w.large largeRequired <;>
      cases smallParity : hedgeNodeXor w.small smallRequired
  · unfold HedgeWitness.largeCarrierDefectBit
      HedgeWitness.smallCarrierDefectBit
    simpa [largeRequired, smallRequired] using largeParity.trans smallParity.symm
  · have largeEven :=
        (hedgeNodeXor_eq_false_iff_even w.large largeRequired).mp largeParity
    have smallEven := parityIff.mp largeEven
    have expected :=
      (hedgeNodeXor_eq_false_iff_even w.small smallRequired).mpr smallEven
    rw [smallParity] at expected
    contradiction
  · have smallEven :=
        (hedgeNodeXor_eq_false_iff_even w.small smallRequired).mp smallParity
    have largeEven := parityIff.mpr smallEven
    have expected :=
      (hedgeNodeXor_eq_false_iff_even w.large largeRequired).mpr largeEven
    rw [largeParity] at expected
    contradiction
  · unfold HedgeWitness.largeCarrierDefectBit
      HedgeWitness.smallCarrierDefectBit
    simpa [largeRequired, smallRequired] using largeParity.trans smallParity.symm

/-- Corrected large and nested pair-root fibers have equal cardinality for
every full-alphabet observed target. -/
theorem HedgeWitness.carrierDefectPairBitRealizers_length_eq
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    ((hedgePairBitEnum G).filter
      (hedgePairBitsRealizes G w.large
        (w.largeCarrierDefectIncidence rich target))).length =
      ((hedgePairBitEnum G).filter
        (hedgeNestedPairBitsRealizes G w.large w.small
          (w.smallCarrierDefectIncidence rich target))).length :=
  w.large_forest.component.pairBitRealizers_length_eq_nested G
    w.large w.small w.small_forest.component w.small_subset_large
    (w.largeCarrierDefectIncidence rich target)
    (w.smallCarrierDefectIncidence rich target)
    (w.largeCarrierDefectIncidence_even rich target)
    (w.smallCarrierDefectIncidence_even rich target)

/-!
### Finite support of the positive carrier pair

The old parity models ignored private coordinates inside the selected forest.
The carrier models use those coordinates as background labels, so their
observational fibers need a slightly richer common private-coordinate test.
At a forest node, the structural equations and the fixed defect determine the
target's `second` bit; the private coordinate may be any background that the
carrier maps to the requested value.  Outside the forest, the mechanism
returns the decoded background itself.

Crucially, this private condition is identical for the large and nested
models.  Their only different finite factor is therefore still the pair-root
fiber, whose cardinalities were equated immediately above.
-/

/-- Boolean test for private coordinates compatible with a carrier target.
Inside `outer`, it records the complete fiber of `hedgeParityCarrierValue`;
outside `outer`, it records the unique enumeration index of the target. -/
def hedgeCarrierPrivateCoordinatesFit
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (privateCoordinates : HedgePrivateCoordinates S) : Bool :=
  (List.finRange S.count).all fun child =>
    let background :=
      hedgePrivateDecode S child (privateCoordinates child)
    if outer child then
      decide (hedgeParityCarrierValue rich child
        (hedgeIsSecond rich child (target child)) background = target child)
    else
      decide (background = target child)

/-- Recover the carrier equation tested at a selected forest node. -/
theorem hedgeCarrierPrivateCoordinatesFit_inside
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (privateCoordinates : HedgePrivateCoordinates S)
    (fits : hedgeCarrierPrivateCoordinatesFit rich outer target
      privateCoordinates = true)
    (child : Fin S.count) (inside : outer child = true) :
    hedgeParityCarrierValue rich child
        (hedgeIsSecond rich child (target child))
        (hedgePrivateDecode S child (privateCoordinates child)) =
      target child := by
  have tested := (List.all_eq_true.mp fits) child (List.mem_finRange child)
  simpa [hedgeCarrierPrivateCoordinatesFit, inside] using tested

/-- Recover the direct background equation tested outside the forest. -/
theorem hedgeCarrierPrivateCoordinatesFit_outside
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (privateCoordinates : HedgePrivateCoordinates S)
    (fits : hedgeCarrierPrivateCoordinatesFit rich outer target
      privateCoordinates = true)
    (child : Fin S.count) (outside : outer child = false) :
    hedgePrivateDecode S child (privateCoordinates child) = target child := by
  have tested := (List.all_eq_true.mp fits) child (List.mem_finRange child)
  simpa [hedgeCarrierPrivateCoordinatesFit, outside] using tested

/-- Assemble the common private-coordinate test from its inside and outside
equations. -/
theorem hedgeCarrierPrivateCoordinatesFit_of
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (privateCoordinates : HedgePrivateCoordinates S)
    (inside : forall child, outer child = true →
      hedgeParityCarrierValue rich child
          (hedgeIsSecond rich child (target child))
          (hedgePrivateDecode S child (privateCoordinates child)) =
        target child)
    (outside : forall child, outer child = false →
      hedgePrivateDecode S child (privateCoordinates child) = target child) :
    hedgeCarrierPrivateCoordinatesFit rich outer target
      privateCoordinates = true := by
  unfold hedgeCarrierPrivateCoordinatesFit
  apply List.all_eq_true.mpr
  intro child _member
  cases selected : outer child
  · simpa [selected] using outside child selected
  · simpa [selected] using inside child selected

/-- Exhaustive duplicate-free enumeration of the private carrier fiber. -/
def hedgeCarrierPrivateSupportEnum
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment) : List (HedgePrivateCoordinates S) :=
  (hedgePrivateCoordinateEnum S).filter
    (hedgeCarrierPrivateCoordinatesFit rich outer target)

theorem hedgeCarrierPrivateSupportEnum_nodup
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment) :
    (hedgeCarrierPrivateSupportEnum rich outer target).Nodup :=
  List.Sublist.nodup List.filter_sublist
    (hedgePrivateCoordinateEnum_nodup S)

/-- Reassemble all old hedge assignments satisfying an arbitrary pair-root
test and the common carrier-background test. -/
def hedgeCarrierCoordinateSupportLatents (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool) :
    List (hedgeLatentExtension G).Assignment :=
  (Probability.ConstructivePermutation.pairList
      ((hedgePairBitEnum G).filter pairTest)
      (hedgeCarrierPrivateSupportEnum rich outer target)).map
    (hedgeLatentOfCoordinatePair G)

/-- The old-coordinate carrier support is duplicate-free. -/
theorem hedgeCarrierCoordinateSupportLatents_nodup (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool) :
    (hedgeCarrierCoordinateSupportLatents G rich outer target pairTest).Nodup := by
  unfold hedgeCarrierCoordinateSupportLatents
  apply Probability.ConstructivePermutation.nodup_map_of_injective_on
      (hedgeLatentOfCoordinatePair G) _
  · intro left _leftMem right _rightMem equal
    exact hedgeLatentOfCoordinatePair_injective G equal
  · exact Probability.ConstructivePermutation.pairList_nodup _ _
      (List.Sublist.nodup List.filter_sublist (hedgePairBitEnum_nodup G))
      (hedgeCarrierPrivateSupportEnum_nodup rich outer target)

/-- The carrier support cardinality factors into its pair and private blocks. -/
theorem hedgeCarrierCoordinateSupportLatents_length (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool) :
    (hedgeCarrierCoordinateSupportLatents G rich outer target pairTest).length =
      ((hedgePairBitEnum G).filter pairTest).length *
        (hedgeCarrierPrivateSupportEnum rich outer target).length := by
  unfold hedgeCarrierCoordinateSupportLatents
  rw [List.length_map,
    Probability.ConstructivePermutation.pairList_length]

/-- Membership in the carrier coordinate support is exactly the conjunction
of its pair-root and private-background tests. -/
theorem hedgeCarrierCoordinateSupportLatents_mem_iff (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool)
    (u : (hedgeLatentExtension G).Assignment) :
    u ∈ hedgeCarrierCoordinateSupportLatents G rich outer target pairTest ↔
      pairTest (hedgePairBitsOf G u) = true ∧
        hedgeCarrierPrivateCoordinatesFit rich outer target
          (hedgePrivateCoordinatesOf G u) = true := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨coordinates, coordinatesMem, equal⟩
    have parts :=
      (Probability.ConstructivePermutation.mem_pairList
        coordinates.1 coordinates.2
        ((hedgePairBitEnum G).filter pairTest)
        (hedgeCarrierPrivateSupportEnum rich outer target)).mp coordinatesMem
    have pairParts := List.mem_filter.mp parts.1
    have privateParts := List.mem_filter.mp parts.2
    rw [← equal]
    constructor
    · simpa [hedgeLatentOfCoordinatePair,
        hedgePairBitsOf_latentOfCoordinates] using pairParts.2
    · simpa [hedgeLatentOfCoordinatePair,
        hedgePrivateCoordinatesOf_latentOfCoordinates,
        hedgeCarrierPrivateSupportEnum] using privateParts.2
  · intro parts
    apply List.mem_map.mpr
    refine ⟨(hedgePairBitsOf G u, hedgePrivateCoordinatesOf G u), ?_, ?_⟩
    · apply (Probability.ConstructivePermutation.mem_pairList
        (hedgePairBitsOf G u) (hedgePrivateCoordinatesOf G u)
        ((hedgePairBitEnum G).filter pairTest)
        (hedgeCarrierPrivateSupportEnum rich outer target)).mpr
      constructor
      · exact List.mem_filter.mpr
          ⟨hedgePairBitEnum_complete G (hedgePairBitsOf G u), parts.1⟩
      · exact List.mem_filter.mpr
          ⟨hedgePrivateCoordinateEnum_complete S
              (hedgePrivateCoordinatesOf G u), parts.2⟩
    · exact hedgeLatentOfCoordinates_recover G u

/-- Project an augmented assignment onto its old successor coordinates. -/
def hedgeDefectOldAssignment (G : ObservedGraph S)
    (u : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :
    (hedgeLatentExtension G).Assignment :=
  fun root => cast (hedgeDefectLatentValue_succ G root) (u root.succ)

/-- Read the distinguished zero-coordinate defect from an augmented
assignment. -/
def hedgeDefectBitOf (G : ObservedGraph S)
    (u : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) : Bool :=
  cast (hedgeDefectLatentValue_zero G) (u (hedgeDefectRoot G))

@[simp] theorem hedgeDefectOldAssignment_assignment (G : ObservedGraph S)
    (old : (hedgeLatentExtension G).Assignment) (defect : Bool) :
    hedgeDefectOldAssignment G (hedgeDefectAssignment G old defect) = old := by
  funext root
  exact hedgeDefectAssignment_succ G old defect root

@[simp] theorem hedgeDefectBitOf_assignment (G : ObservedGraph S)
    (old : (hedgeLatentExtension G).Assignment) (defect : Bool) :
    hedgeDefectBitOf G (hedgeDefectAssignment G old defect) = defect :=
  hedgeDefectAssignment_zero G old defect

/-- The two projections reconstruct every augmented assignment. -/
theorem hedgeDefectAssignment_recover (G : ObservedGraph S)
    (u : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :
    hedgeDefectAssignment G (hedgeDefectOldAssignment G u)
        (hedgeDefectBitOf G u) =
      u := by
  funext root
  refine Fin.cases ?_ (fun old => ?_) root
  · have recovered := hedgeDefectAssignment_zero G
      (hedgeDefectOldAssignment G u) (hedgeDefectBitOf G u)
    unfold hedgeDefectBitOf at recovered
    exact cast_injective_value (hedgeDefectLatentValue_zero G) recovered
  · have recovered := hedgeDefectAssignment_succ G
      (hedgeDefectOldAssignment G u) (hedgeDefectBitOf G u) old
    unfold hedgeDefectOldAssignment at recovered
    exact cast_injective_value (hedgeDefectLatentValue_succ G old) recovered

/-- Prefixing the same defect bit is injective in the old latent assignment. -/
theorem hedgeDefectAssignment_injective_old (G : ObservedGraph S)
    (defect : Bool) {left right : (hedgeLatentExtension G).Assignment}
    (equal : hedgeDefectAssignment G left defect =
      hedgeDefectAssignment G right defect) :
    left = right := by
  funext root
  have atRoot := congrFun equal root.succ
  have transported := congrArg
    (cast (hedgeDefectLatentValue_succ G root)) atRoot
  simpa using transported

/-- Prefix the fixed target defect onto every old-coordinate support point. -/
def hedgeCarrierDefectSupportLatents (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool)
    (defect : Bool) :
    List ((root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :=
  (hedgeCarrierCoordinateSupportLatents G rich outer target pairTest).map
    (fun old => hedgeDefectAssignment G old defect)

/-- Prefixing preserves duplicate-freeness of the factored support. -/
theorem hedgeCarrierDefectSupportLatents_nodup (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool)
    (defect : Bool) :
    (hedgeCarrierDefectSupportLatents G rich outer target pairTest defect).Nodup := by
  unfold hedgeCarrierDefectSupportLatents
  apply Probability.ConstructivePermutation.nodup_map_of_injective_on
      (fun old => hedgeDefectAssignment G old defect) _
  · intro left _leftMem right _rightMem equal
    exact hedgeDefectAssignment_injective_old G defect equal
  · exact hedgeCarrierCoordinateSupportLatents_nodup G rich outer target
      pairTest

/-- Prefixing changes no list cardinality. -/
theorem hedgeCarrierDefectSupportLatents_length (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool)
    (defect : Bool) :
    (hedgeCarrierDefectSupportLatents G rich outer target pairTest defect).length =
      ((hedgePairBitEnum G).filter pairTest).length *
        (hedgeCarrierPrivateSupportEnum rich outer target).length := by
  rw [hedgeCarrierDefectSupportLatents, List.length_map,
    hedgeCarrierCoordinateSupportLatents_length]

/-- Membership in an augmented support fixes the defect coordinate and then
reduces to membership of the projected old assignment. -/
theorem hedgeCarrierDefectSupportLatents_mem_iff (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool)
    (defect : Bool)
    (u : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :
    u ∈ hedgeCarrierDefectSupportLatents G rich outer target pairTest defect ↔
      hedgeDefectBitOf G u = defect ∧
        hedgeDefectOldAssignment G u ∈
          hedgeCarrierCoordinateSupportLatents G rich outer target pairTest := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨old, oldMem, equal⟩
    rw [← equal]
    exact ⟨hedgeDefectBitOf_assignment G old defect,
      hedgeDefectOldAssignment_assignment G old defect ▸ oldMem⟩
  · intro parts
    apply List.mem_map.mpr
    refine ⟨hedgeDefectOldAssignment G u, parts.2, ?_⟩
    rw [← parts.1]
    exact hedgeDefectAssignment_recover G u

/-- Complete candidate observational fiber of the large carrier model at one
target.  Subsequent semantic lemmas show that this finite list is exact. -/
def HedgeWitness.largeCarrierDefectObservationalSupport
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    List (w.largeCarrierDefectParityModel rich).latent.Assignment :=
  hedgeCarrierDefectSupportLatents G rich w.large target
    (hedgePairBitsRealizes G w.large
      (w.largeCarrierDefectIncidence rich target))
    (w.largeCarrierDefectBit rich target)

/-- Complete candidate observational fiber of the nested carrier model. -/
def HedgeWitness.smallCarrierDefectObservationalSupport
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    List (w.smallCarrierDefectParityModel rich).latent.Assignment :=
  hedgeCarrierDefectSupportLatents G rich w.large target
    (hedgeNestedPairBitsRealizes G w.large w.small
      (w.smallCarrierDefectIncidence rich target))
    (w.smallCarrierDefectBit rich target)

/-- The large candidate fiber contains no duplicate latent assignments. -/
theorem HedgeWitness.largeCarrierDefectObservationalSupport_nodup
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (w.largeCarrierDefectObservationalSupport rich target).Nodup := by
  simpa [HedgeWitness.largeCarrierDefectObservationalSupport,
    HedgeWitness.largeCarrierDefectParityModel, hedgeCarrierDefectModel] using
      hedgeCarrierDefectSupportLatents_nodup G rich w.large target
        (hedgePairBitsRealizes G w.large
          (w.largeCarrierDefectIncidence rich target))
        (w.largeCarrierDefectBit rich target)

/-- The nested candidate fiber contains no duplicate latent assignments. -/
theorem HedgeWitness.smallCarrierDefectObservationalSupport_nodup
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (w.smallCarrierDefectObservationalSupport rich target).Nodup := by
  simpa [HedgeWitness.smallCarrierDefectObservationalSupport,
    HedgeWitness.smallCarrierDefectParityModel, hedgeCarrierDefectModel] using
      hedgeCarrierDefectSupportLatents_nodup G rich w.large target
        (hedgeNestedPairBitsRealizes G w.large w.small
          (w.smallCarrierDefectIncidence rich target))
        (w.smallCarrierDefectBit rich target)

/-- The large and nested candidate observational fibers have equal size.
The common private-background factor remains visible, while the pair-root
factor is exactly `carrierDefectPairBitRealizers_length_eq`. -/
theorem HedgeWitness.carrierDefectObservationalSupport_length_eq
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    (w.largeCarrierDefectObservationalSupport rich target).length =
      (w.smallCarrierDefectObservationalSupport rich target).length := by
  simp only [HedgeWitness.largeCarrierDefectObservationalSupport,
    HedgeWitness.smallCarrierDefectObservationalSupport,
    HedgeWitness.largeCarrierDefectParityModel,
    HedgeWitness.smallCarrierDefectParityModel,
    hedgeCarrierDefectModel, hedgeDefectLatentExtension,
    hedgeCarrierDefectSupportLatents]
  rw [List.length_map
      (fun old => hedgeDefectAssignment G old
        (w.largeCarrierDefectBit rich target)),
    List.length_map
      (fun old => hedgeDefectAssignment G old
        (w.smallCarrierDefectBit rich target))]
  rw [
    hedgeCarrierCoordinateSupportLatents_length,
    hedgeCarrierCoordinateSupportLatents_length,
    w.carrierDefectPairBitRealizers_length_eq rich target]

/-!
### Exact semantic support

The remaining direction is semantic rather than combinatorial.  We first
state the correction with an arbitrary defect bit.  An incidence vector
realized by pair roots is even, so the only defect that can correct a target
is its selected XOR.  This proves that evaluation fixes the zero coordinate
to the canonical defect used in the support lists.
-/

/-- Toggle one anchor of an incidence target by an explicitly supplied
defect bit. -/
def hedgeDefectAdjustedTargetBy {S : ObservedSignature}
    (anchor : Fin S.count) (defect : Bool)
    (target : Fin S.count → Bool) (node : Fin S.count) : Bool :=
  Bool.xor (target node) (if node = anchor then defect else false)

/-- XOR of an explicitly corrected target is the original XOR followed by
the supplied defect, provided the anchor belongs to the selected nodes. -/
theorem hedgeNodeXor_adjustedTargetBy (nodes : NodeSet S)
    (anchor : Fin S.count) (inside : nodes anchor = true) (defect : Bool)
    (target : Fin S.count → Bool) :
    hedgeNodeXor nodes (hedgeDefectAdjustedTargetBy anchor defect target) =
      Bool.xor (hedgeNodeXor nodes target) defect := by
  unfold hedgeDefectAdjustedTargetBy hedgeNodeXor
  rw [foldl_xor_pointwise]
  change Bool.xor
      ((NodeSet.members nodes).foldl
        (fun total node => Bool.xor total (target node)) false)
      (hedgeNodeXor nodes
        (fun node => if node = anchor then defect else false)) = _
  rw [hedgeNodeXor_singleAnchor nodes anchor inside defect]

/-- An even explicitly corrected target determines its defect uniquely. -/
theorem hedgeDefect_eq_nodeXor_of_adjusted_even (nodes : NodeSet S)
    (anchor : Fin S.count) (inside : nodes anchor = true) (defect : Bool)
    (target : Fin S.count → Bool)
    (even : (hedgeTrueVertices nodes
      (hedgeDefectAdjustedTargetBy anchor defect target)).length % 2 = 0) :
    defect = hedgeNodeXor nodes target := by
  have correctedFalse :
      hedgeNodeXor nodes
          (hedgeDefectAdjustedTargetBy anchor defect target) = false :=
    (hedgeNodeXor_eq_false_iff_even nodes
      (hedgeDefectAdjustedTargetBy anchor defect target)).mpr even
  rw [hedgeNodeXor_adjustedTargetBy nodes anchor inside defect target]
    at correctedFalse
  generalize hedgeNodeXor nodes target = parity at correctedFalse ⊢
  cases defect <;> cases parity <;> simp at correctedFalse ⊢

/-- The existing canonical correction is the explicit correction by the
target's selected XOR. -/
theorem hedgeDefectAdjustedTarget_eq_by (nodes : NodeSet S)
    (anchor : Fin S.count) (target : Fin S.count → Bool) :
    hedgeDefectAdjustedTarget nodes anchor target =
      hedgeDefectAdjustedTargetBy anchor (hedgeNodeXor nodes target) target :=
  rfl

/-- Projected old inputs are precisely the successor-coordinate projection
of the complete augmented assignment. -/
theorem hedgeDefectOldInputs_eq_oldAssignment (G : ObservedGraph S)
    (defectNode child : Fin S.count)
    (u : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :
    hedgeDefectOldInputs G defectNode child (fun root _incident => u root) =
      (fun root _incident => hedgeDefectOldAssignment G u root) := by
  funext root incident
  rfl

/-- At an arbitrary augmented assignment, the private defect is visible only
at its unique observed child. -/
theorem hedgeIndependentDefectBit_eq_bitOf (G : ObservedGraph S)
    (defectNode child : Fin S.count)
    (u : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :
    hedgeIndependentDefectBit G defectNode child
        (fun root _incident => u root) =
      if child = defectNode then hedgeDefectBitOf G u else false := by
  by_cases equal : child = defectNode
  · subst child
    simp [hedgeIndependentDefectBit, hedgeDefectBitOf]
  · simp [hedgeIndependentDefectBit, equal]

/-- Pair roots of an arbitrary large-carrier evaluation realize the target
incidence corrected by that assignment's actual private defect. -/
theorem HedgeWitness.largeCarrierDefectPairBitsRealizes_evalBy
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (w.largeCarrierDefectParityModel rich).latent.Assignment) :
    hedgePairBitsRealizes G w.large
        (hedgeDefectAdjustedTargetBy w.actionRoot (hedgeDefectBitOf G u)
          (hedgeForestRequiredIncidence rich w.child
            ((w.largeCarrierDefectParityModel rich).eval u)))
        (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) = true := by
  apply hedgePairBitsRealizes_of
  intro child inside
  rw [← hedgeXorPairBitsWithin_pairBitsOf G w.large
    (hedgeDefectOldAssignment G u) child]
  have oldInputsEq := hedgeDefectOldInputs_eq_oldAssignment G w.actionRoot
    child u
  have defectAt := hedgeIndependentDefectBit_eq_bitOf G w.actionRoot child u
  have carrierBit := hedgeCarrierDefectModel_evalNodeUnder_bit G rich
    w.actionRoot (w.largeParityModel rich).mechanism
    (FiniteLatentSCM.noIntervention S) u child rfl
  change hedgeIsSecond rich child
      ((w.largeCarrierDefectParityModel rich).eval u child) =
    Bool.xor
      (hedgeIsSecond rich child
        ((w.largeParityModel rich).mechanism child
          (fun parent _edge =>
            (w.largeCarrierDefectParityModel rich).eval u parent)
          (hedgeDefectOldInputs G w.actionRoot child
            (fun root _incident => u root))))
      (hedgeIndependentDefectBit G w.actionRoot child
        (fun root _incident => u root)) at carrierBit
  have baseBit := hedgeForestParityOutput_bit_of_mem G rich w.large w.child
    child
    (fun parent _edge =>
      (w.largeCarrierDefectParityModel rich).eval u parent)
    (fun root _incident => hedgeDefectOldAssignment G u root) inside
  change hedgeIsSecond rich child
      ((w.largeParityModel rich).mechanism child
        (fun parent _edge =>
          (w.largeCarrierDefectParityModel rich).eval u parent)
        (fun root _incident => hedgeDefectOldAssignment G u root)) = _
    at baseBit
  rw [oldInputsEq, defectAt] at carrierBit
  unfold hedgeDefectAdjustedTargetBy hedgeForestRequiredIncidence
  have cancel (output structural pair parents defect : Bool)
      (outputEq : output = Bool.xor structural defect)
      (structuralEq : structural = Bool.xor pair parents) :
      pair = Bool.xor (Bool.xor output parents) defect := by
    rw [outputEq, structuralEq]
    cases pair <;> cases parents <;> cases defect <;> rfl
  apply cancel
  · exact carrierBit
  · exact baseBit

/-- Evaluation forces the augmented assignment's defect to be the canonical
large-forest correction bit of its observed output. -/
theorem HedgeWitness.largeCarrierDefectBitOf_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (w.largeCarrierDefectParityModel rich).latent.Assignment) :
    hedgeDefectBitOf G u =
      w.largeCarrierDefectBit rich
        ((w.largeCarrierDefectParityModel rich).eval u) := by
  have realizes := w.largeCarrierDefectPairBitsRealizes_evalBy rich u
  have even := hedgePairBitsRealizes_even G w.large
    (hedgeDefectAdjustedTargetBy w.actionRoot (hedgeDefectBitOf G u)
      (hedgeForestRequiredIncidence rich w.child
        ((w.largeCarrierDefectParityModel rich).eval u)))
    (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) realizes
  exact hedgeDefect_eq_nodeXor_of_adjusted_even w.large w.actionRoot
    w.actionRoot_in_large (hedgeDefectBitOf G u)
    (hedgeForestRequiredIncidence rich w.child
      ((w.largeCarrierDefectParityModel rich).eval u)) even

/-- After replacing the forced defect by its canonical expression, the old
pair coordinates realize the exact large support predicate. -/
theorem HedgeWitness.largeCarrierDefectPairBitsRealizes_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (w.largeCarrierDefectParityModel rich).latent.Assignment) :
    hedgePairBitsRealizes G w.large
        (w.largeCarrierDefectIncidence rich
          ((w.largeCarrierDefectParityModel rich).eval u))
        (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) = true := by
  have realizes := w.largeCarrierDefectPairBitsRealizes_evalBy rich u
  have defect := w.largeCarrierDefectBitOf_eval rich u
  simpa [HedgeWitness.largeCarrierDefectIncidence,
    hedgeDefectAdjustedTarget_eq_by, HedgeWitness.largeCarrierDefectBit,
    defect] using realizes

/-- Private coordinates of a large-carrier evaluation satisfy the common
background fiber predicate. -/
theorem HedgeWitness.largeCarrierPrivateCoordinatesFit_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (w.largeCarrierDefectParityModel rich).latent.Assignment) :
    hedgeCarrierPrivateCoordinatesFit rich w.large
        ((w.largeCarrierDefectParityModel rich).eval u)
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G u)) = true := by
  apply hedgeCarrierPrivateCoordinatesFit_of
  · intro child inside
    have oldInputsEq := hedgeDefectOldInputs_eq_oldAssignment G w.actionRoot
      child u
    have defectAt := hedgeIndependentDefectBit_eq_bitOf G w.actionRoot child u
    have outputEq :
        (w.largeCarrierDefectParityModel rich).eval u child =
          hedgeParityCarrierValue rich child
            (Bool.xor
              (hedgeIsSecond rich child
                ((w.largeParityModel rich).mechanism child
                  (fun parent _edge =>
                    (w.largeCarrierDefectParityModel rich).eval u parent)
                  (fun root _incident =>
                    hedgeDefectOldAssignment G u root)))
              (if child = w.actionRoot then hedgeDefectBitOf G u else false))
            (hedgePrivateDecode S child
              ((hedgePrivateCoordinatesOf G
                (hedgeDefectOldAssignment G u)) child)) := by
      change (w.largeCarrierDefectParityModel rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child = _
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      simp only [HedgeWitness.largeCarrierDefectParityModel,
        hedgeCarrierDefectModel]
      rw [oldInputsEq, defectAt]
      rfl
    have outputBit := congrArg (hedgeIsSecond rich child) outputEq
    rw [hedgeIsSecond_parityCarrierValue] at outputBit
    rw [outputBit]
    exact outputEq.symm
  · intro child outside
    have different : child ≠ w.actionRoot := by
      intro equal
      subst child
      rw [w.actionRoot_in_large] at outside
      contradiction
    have oldInputsEq := hedgeDefectOldInputs_eq_oldAssignment G w.actionRoot
      child u
    have defectAt := hedgeIndependentDefectBit_eq_bitOf G w.actionRoot child u
    have outputEq :
        (w.largeCarrierDefectParityModel rich).eval u child =
          hedgeParityCarrierValue rich child
            (Bool.xor
              (hedgeIsSecond rich child
                ((w.largeParityModel rich).mechanism child
                  (fun parent _edge =>
                    (w.largeCarrierDefectParityModel rich).eval u parent)
                  (fun root _incident =>
                    hedgeDefectOldAssignment G u root)))
              (if child = w.actionRoot then hedgeDefectBitOf G u else false))
            (hedgePrivateDecode S child
              ((hedgePrivateCoordinatesOf G
                (hedgeDefectOldAssignment G u)) child)) := by
      change (w.largeCarrierDefectParityModel rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child = _
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      simp only [HedgeWitness.largeCarrierDefectParityModel,
        hedgeCarrierDefectModel]
      rw [oldInputsEq, defectAt]
      rfl
    have baseOutside :
        (w.largeParityModel rich).mechanism child
            (fun parent _edge =>
              (w.largeCarrierDefectParityModel rich).eval u parent)
            (fun root _incident => hedgeDefectOldAssignment G u root) =
          hedgePrivateDecode S child
            ((hedgePrivateCoordinatesOf G
              (hedgeDefectOldAssignment G u)) child) := by
      simp [HedgeWitness.largeParityModel, hedgeForestParityModel,
        hedgeForestParityOutput, outside, hedgePrivateCoordinatesOf]
    rw [baseOutside] at outputEq
    simp [different, hedgeParityCarrierValue_reconstruct] at outputEq
    exact outputEq.symm

/-- Conversely, the three finite support conditions determine evaluation of
the large carrier model.  The proof follows the observed topological order so
that every kept-parent value is already the requested target value. -/
theorem HedgeWitness.largeCarrierDefectParityModel_evalNode_eq_of_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (u : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (defectEq : hedgeDefectBitOf G u =
      w.largeCarrierDefectBit rich target)
    (realizes : hedgePairBitsRealizes G w.large
      (w.largeCarrierDefectIncidence rich target)
      (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) = true)
    (privateFits : hedgeCarrierPrivateCoordinatesFit rich w.large target
      (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G u)) = true)
    (child : Fin S.count) :
    (w.largeCarrierDefectParityModel rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child = target child := by
  have oldInputsEq := hedgeDefectOldInputs_eq_oldAssignment G w.actionRoot
    child u
  have defectAt := hedgeIndependentDefectBit_eq_bitOf G w.actionRoot child u
  have outputEq :
      (w.largeCarrierDefectParityModel rich).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child =
        hedgeParityCarrierValue rich child
          (Bool.xor
            (hedgeIsSecond rich child
              ((w.largeParityModel rich).mechanism child
                (fun parent _edge =>
                  (w.largeCarrierDefectParityModel rich).evalNodeUnder
                    (FiniteLatentSCM.noIntervention S) u parent)
                (fun root _incident =>
                  hedgeDefectOldAssignment G u root)))
            (if child = w.actionRoot then hedgeDefectBitOf G u else false))
          (hedgePrivateDecode S child
            ((hedgePrivateCoordinatesOf G
              (hedgeDefectOldAssignment G u)) child)) := by
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    simp only [HedgeWitness.largeCarrierDefectParityModel,
      hedgeCarrierDefectModel]
    rw [oldInputsEq, defectAt]
    rfl
  cases selected : w.large child with
  | false =>
      have different : child ≠ w.actionRoot := by
        intro equal
        subst child
        rw [w.actionRoot_in_large] at selected
        contradiction
      have baseOutside :
          (w.largeParityModel rich).mechanism child
              (fun parent _edge =>
                (w.largeCarrierDefectParityModel rich).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent)
              (fun root _incident => hedgeDefectOldAssignment G u root) =
            hedgePrivateDecode S child
              ((hedgePrivateCoordinatesOf G
                (hedgeDefectOldAssignment G u)) child) := by
        simp [HedgeWitness.largeParityModel, hedgeForestParityModel,
          hedgeForestParityOutput, selected, hedgePrivateCoordinatesOf]
      rw [outputEq, baseOutside]
      simp only [different, if_false, Bool.xor_false]
      rw [hedgeParityCarrierValue_reconstruct]
      exact hedgeCarrierPrivateCoordinatesFit_outside rich w.large target
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G u))
        privateFits child selected
  | true =>
      have parentsEq :
          hedgeForestParentBitsFrom rich w.child child
              (fun parent edge =>
                (w.largeCarrierDefectParityModel rich).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent) =
            hedgeForestParentBitsFrom rich w.child child
              (fun parent _edge => target parent) := by
        exact hedgeForestParentBitsFrom_congr rich child
          (fun _parent => rfl)
          (fun parent edge =>
            w.largeCarrierDefectParityModel_evalNode_eq_of_support rich target
              u defectEq realizes privateFits parent)
      have pairEq :
          hedgeXorPairBitsWithin G w.large child
              (fun root _incident => hedgeDefectOldAssignment G u root) =
            w.largeCarrierDefectIncidence rich target child := by
        rw [hedgeXorPairBitsWithin_pairBitsOf]
        exact hedgePairBitsRealizes_spec G w.large
          (w.largeCarrierDefectIncidence rich target)
          (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) realizes child
          selected
      have baseBit := hedgeForestParityOutput_bit_of_mem G rich w.large
        w.child child
        (fun parent edge =>
          (w.largeCarrierDefectParityModel rich).evalNodeUnder
            (FiniteLatentSCM.noIntervention S) u parent)
        (fun root _incident => hedgeDefectOldAssignment G u root) selected
      change hedgeIsSecond rich child
          ((w.largeParityModel rich).mechanism child
            (fun parent edge =>
              (w.largeCarrierDefectParityModel rich).evalNodeUnder
                (FiniteLatentSCM.noIntervention S) u parent)
            (fun root _incident => hedgeDefectOldAssignment G u root)) = _
        at baseBit
      rw [outputEq]
      refine (congrArg
        (fun bit => hedgeParityCarrierValue rich child bit
          (hedgePrivateDecode S child
            ((hedgePrivateCoordinatesOf G
              (hedgeDefectOldAssignment G u)) child))) ?_).trans
        (hedgeCarrierPrivateCoordinatesFit_inside rich w.large target
          (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G u))
          privateFits child selected)
      rw [baseBit, pairEq, parentsEq, defectEq]
      unfold HedgeWitness.largeCarrierDefectIncidence
        hedgeDefectAdjustedTarget HedgeWitness.largeCarrierDefectBit
        hedgeForestRequiredIncidence
      by_cases equal : child = w.actionRoot <;>
        simp only [equal, if_true, if_false]
      all_goals
        generalize hedgeIsSecond rich child (target child) = output
        generalize hedgeForestParentBitsFrom rich w.child child
          (fun parent _edge => target parent) = parents
        generalize hedgeNodeXor w.large (fun node =>
          Bool.xor (hedgeIsSecond rich node (target node))
            (hedgeForestParentBitsFrom rich w.child node
              (fun parent _edge => target parent))) = parity
        cases output <;> cases parents <;> cases parity <;> rfl
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

/-- Complete evaluation follows from membership in the large finite support
predicate. -/
theorem HedgeWitness.largeCarrierDefectParityModel_eval_eq_of_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (u : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (defectEq : hedgeDefectBitOf G u =
      w.largeCarrierDefectBit rich target)
    (realizes : hedgePairBitsRealizes G w.large
      (w.largeCarrierDefectIncidence rich target)
      (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) = true)
    (privateFits : hedgeCarrierPrivateCoordinatesFit rich w.large target
      (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G u)) = true) :
    (w.largeCarrierDefectParityModel rich).eval u = target := by
  funext child
  exact w.largeCarrierDefectParityModel_evalNode_eq_of_support rich target u
    defectEq realizes privateFits child

/-- Large-carrier evaluation is exactly membership in the finite support list
used for observational counting. -/
theorem HedgeWitness.largeCarrierDefectParityModel_eval_mem_support_iff
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (u : (w.largeCarrierDefectParityModel rich).latent.Assignment) :
    (w.largeCarrierDefectParityModel rich).eval u = target ↔
      u ∈ w.largeCarrierDefectObservationalSupport rich target := by
  change ((root : Fin (hedgeDefectLatentCount G)) →
    hedgeDefectLatentValue G root) at u
  change (w.largeCarrierDefectParityModel rich).eval u = target ↔
    u ∈ hedgeCarrierDefectSupportLatents G rich w.large target
      (hedgePairBitsRealizes G w.large
        (w.largeCarrierDefectIncidence rich target))
      (w.largeCarrierDefectBit rich target)
  rw [hedgeCarrierDefectSupportLatents_mem_iff,
    hedgeCarrierCoordinateSupportLatents_mem_iff]
  constructor
  · intro evaluates
    subst target
    exact ⟨w.largeCarrierDefectBitOf_eval rich u,
      w.largeCarrierDefectPairBitsRealizes_eval rich u,
      w.largeCarrierPrivateCoordinatesFit_eval rich u⟩
  · intro support
    exact w.largeCarrierDefectParityModel_eval_eq_of_support rich target u
      support.1 support.2.1 support.2.2

/-! #### Exact support of the nested carrier -/

/-- Pair roots of an arbitrary nested-carrier evaluation realize the nested
target incidence corrected by that assignment's actual defect. -/
theorem HedgeWitness.smallCarrierDefectPairBitsRealizes_evalBy
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (w.smallCarrierDefectParityModel rich).latent.Assignment) :
    hedgeNestedPairBitsRealizes G w.large w.small
        (hedgeDefectAdjustedTargetBy w.actionRoot (hedgeDefectBitOf G u)
          (hedgeNestedForestRequiredIncidence rich w.small w.child
            (restrictChild w.small w.child)
            ((w.smallCarrierDefectParityModel rich).eval u)))
        (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) = true := by
  apply hedgeNestedPairBitsRealizes_of
  intro child inLarge
  have oldInputsEq := hedgeDefectOldInputs_eq_oldAssignment G w.actionRoot
    child u
  have defectAt := hedgeIndependentDefectBit_eq_bitOf G w.actionRoot child u
  have carrierBit := hedgeCarrierDefectModel_evalNodeUnder_bit G rich
    w.actionRoot (w.smallParityModel rich).mechanism
    (FiniteLatentSCM.noIntervention S) u child rfl
  change hedgeIsSecond rich child
      ((w.smallCarrierDefectParityModel rich).eval u child) =
    Bool.xor
      (hedgeIsSecond rich child
        ((w.smallParityModel rich).mechanism child
          (fun parent _edge =>
            (w.smallCarrierDefectParityModel rich).eval u parent)
          (hedgeDefectOldInputs G w.actionRoot child
            (fun root _incident => u root))))
      (hedgeIndependentDefectBit G w.actionRoot child
        (fun root _incident => u root)) at carrierBit
  rw [oldInputsEq, defectAt] at carrierBit
  have cancel (output structural pair parents defect : Bool)
      (outputEq : output = Bool.xor structural defect)
      (structuralEq : structural = Bool.xor pair parents) :
      pair = Bool.xor (Bool.xor output parents) defect := by
    rw [outputEq, structuralEq]
    cases pair <;> cases parents <;> cases defect <;> rfl
  cases inSmall : w.small child with
  | false =>
      simp only [hedgeNestedXorPairBitsWithinFrom, inSmall,
        Bool.false_eq_true, if_false]
      rw [← hedgeXorPairBitsWithin_pairBitsOf G w.large
        (hedgeDefectOldAssignment G u) child]
      have largeBase := hedgeForestParityOutput_bit_of_mem G rich w.large
        w.child child
        (fun parent _edge =>
          (w.smallCarrierDefectParityModel rich).eval u parent)
        (fun root _incident => hedgeDefectOldAssignment G u root) inLarge
      have baseBit :
          hedgeIsSecond rich child
              ((w.smallParityModel rich).mechanism child
                (fun parent _edge =>
                  (w.smallCarrierDefectParityModel rich).eval u parent)
                (fun root _incident => hedgeDefectOldAssignment G u root)) =
            Bool.xor
              (hedgeXorPairBitsWithin G w.large child
                (fun root _incident => hedgeDefectOldAssignment G u root))
              (hedgeForestParentBitsFrom rich w.child child
                (fun parent _edge =>
                  (w.smallCarrierDefectParityModel rich).eval u parent)) := by
        rw [← w.parityMechanism_eq_of_not_small rich child _ _ inSmall]
        exact largeBase
      unfold hedgeNestedForestRequiredIncidence
      unfold hedgeDefectAdjustedTargetBy hedgeForestRequiredIncidence
      dsimp only
      have notSmall : w.small child ≠ true := by
        rw [inSmall]
        simp
      rw [if_neg notSmall]
      change
        hedgeXorPairBitsWithin G w.large child
            (fun root _incident => hedgeDefectOldAssignment G u root) =
          Bool.xor
            (Bool.xor
              (hedgeIsSecond rich child
                ((w.smallCarrierDefectParityModel rich).eval u child))
              (hedgeForestParentBitsFrom rich w.child child
                (fun parent _edge =>
                  (w.smallCarrierDefectParityModel rich).eval u parent)))
            (if child = w.actionRoot then hedgeDefectBitOf G u else false)
      apply cancel
      · exact carrierBit
      · exact baseBit
  | true =>
      simp only [hedgeNestedXorPairBitsWithinFrom, inSmall, if_true]
      rw [← hedgeXorPairBitsWithin_pairBitsOf G w.small
        (hedgeDefectOldAssignment G u) child]
      have smallBase := hedgeForestParityOutput_bit_of_mem G rich w.small
        (restrictChild w.small w.child) child
        (fun parent _edge =>
          (w.smallCarrierDefectParityModel rich).eval u parent)
        (fun root _incident => hedgeDefectOldAssignment G u root) inSmall
      have baseBit :
          hedgeIsSecond rich child
              ((w.smallParityModel rich).mechanism child
                (fun parent _edge =>
                  (w.smallCarrierDefectParityModel rich).eval u parent)
                (fun root _incident => hedgeDefectOldAssignment G u root)) =
            Bool.xor
              (hedgeXorPairBitsWithin G w.small child
                (fun root _incident => hedgeDefectOldAssignment G u root))
              (hedgeForestParentBitsFrom rich
                (restrictChild w.small w.child) child
                (fun parent _edge =>
                  (w.smallCarrierDefectParityModel rich).eval u parent)) := by
        rw [w.smallParityMechanism_of_small rich child _ _ inSmall]
        exact smallBase
      unfold hedgeNestedForestRequiredIncidence
      unfold hedgeDefectAdjustedTargetBy hedgeForestRequiredIncidence
      dsimp only
      rw [if_pos inSmall]
      change
        hedgeXorPairBitsWithin G w.small child
            (fun root _incident => hedgeDefectOldAssignment G u root) =
          Bool.xor
            (Bool.xor
              (hedgeIsSecond rich child
                ((w.smallCarrierDefectParityModel rich).eval u child))
              (hedgeForestParentBitsFrom rich
                (restrictChild w.small w.child) child
                (fun parent _edge =>
                  (w.smallCarrierDefectParityModel rich).eval u parent)))
            (if child = w.actionRoot then hedgeDefectBitOf G u else false)
      apply cancel
      · exact carrierBit
      · exact baseBit

/-- Evaluation forces the nested model's defect to be the canonical inner
small-component correction bit of its observed output. -/
theorem HedgeWitness.smallCarrierDefectBitOf_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (w.smallCarrierDefectParityModel rich).latent.Assignment) :
    hedgeDefectBitOf G u =
      w.smallCarrierDefectBit rich
        ((w.smallCarrierDefectParityModel rich).eval u) := by
  have realizes := w.smallCarrierDefectPairBitsRealizes_evalBy rich u
  have even := hedgeNestedPairBitsRealizes_inner_even G w.large w.small
    w.small_subset_large
    (hedgeDefectAdjustedTargetBy w.actionRoot (hedgeDefectBitOf G u)
      (hedgeNestedForestRequiredIncidence rich w.small w.child
        (restrictChild w.small w.child)
        ((w.smallCarrierDefectParityModel rich).eval u)))
    (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) realizes
  exact hedgeDefect_eq_nodeXor_of_adjusted_even w.small w.actionRoot
    w.actionRoot_in_small (hedgeDefectBitOf G u)
    (hedgeNestedForestRequiredIncidence rich w.small w.child
      (restrictChild w.small w.child)
      ((w.smallCarrierDefectParityModel rich).eval u)) even

/-- Replacing the forced nested defect by its canonical expression gives the
exact pair-root predicate used by the small support list. -/
theorem HedgeWitness.smallCarrierDefectPairBitsRealizes_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (w.smallCarrierDefectParityModel rich).latent.Assignment) :
    hedgeNestedPairBitsRealizes G w.large w.small
        (w.smallCarrierDefectIncidence rich
          ((w.smallCarrierDefectParityModel rich).eval u))
        (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) = true := by
  have realizes := w.smallCarrierDefectPairBitsRealizes_evalBy rich u
  have defect := w.smallCarrierDefectBitOf_eval rich u
  simpa [HedgeWitness.smallCarrierDefectIncidence,
    hedgeDefectAdjustedTarget_eq_by, HedgeWitness.smallCarrierDefectBit,
    defect] using realizes

/-- Private coordinates of a nested-carrier evaluation satisfy the same
background-fiber test as the large model. -/
theorem HedgeWitness.smallCarrierPrivateCoordinatesFit_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (w.smallCarrierDefectParityModel rich).latent.Assignment) :
    hedgeCarrierPrivateCoordinatesFit rich w.large
        ((w.smallCarrierDefectParityModel rich).eval u)
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G u)) = true := by
  apply hedgeCarrierPrivateCoordinatesFit_of
  · intro child inside
    have oldInputsEq := hedgeDefectOldInputs_eq_oldAssignment G w.actionRoot
      child u
    have defectAt := hedgeIndependentDefectBit_eq_bitOf G w.actionRoot child u
    have outputEq :
        (w.smallCarrierDefectParityModel rich).eval u child =
          hedgeParityCarrierValue rich child
            (Bool.xor
              (hedgeIsSecond rich child
                ((w.smallParityModel rich).mechanism child
                  (fun parent _edge =>
                    (w.smallCarrierDefectParityModel rich).eval u parent)
                  (fun root _incident =>
                    hedgeDefectOldAssignment G u root)))
              (if child = w.actionRoot then hedgeDefectBitOf G u else false))
            (hedgePrivateDecode S child
              ((hedgePrivateCoordinatesOf G
                (hedgeDefectOldAssignment G u)) child)) := by
      change (w.smallCarrierDefectParityModel rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child = _
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      simp only [HedgeWitness.smallCarrierDefectParityModel,
        hedgeCarrierDefectModel]
      rw [oldInputsEq, defectAt]
      rfl
    have outputBit := congrArg (hedgeIsSecond rich child) outputEq
    rw [hedgeIsSecond_parityCarrierValue] at outputBit
    rw [outputBit]
    exact outputEq.symm
  · intro child outside
    have inSmall : w.small child = false := by
      cases selected : w.small child
      · rfl
      · have selectedLarge := w.small_subset_large child selected
        rw [outside] at selectedLarge
        contradiction
    have different : child ≠ w.actionRoot := by
      intro equal
      subst child
      rw [w.actionRoot_in_large] at outside
      contradiction
    have oldInputsEq := hedgeDefectOldInputs_eq_oldAssignment G w.actionRoot
      child u
    have defectAt := hedgeIndependentDefectBit_eq_bitOf G w.actionRoot child u
    have outputEq :
        (w.smallCarrierDefectParityModel rich).eval u child =
          hedgeParityCarrierValue rich child
            (Bool.xor
              (hedgeIsSecond rich child
                ((w.smallParityModel rich).mechanism child
                  (fun parent _edge =>
                    (w.smallCarrierDefectParityModel rich).eval u parent)
                  (fun root _incident =>
                    hedgeDefectOldAssignment G u root)))
              (if child = w.actionRoot then hedgeDefectBitOf G u else false))
            (hedgePrivateDecode S child
              ((hedgePrivateCoordinatesOf G
                (hedgeDefectOldAssignment G u)) child)) := by
      change (w.smallCarrierDefectParityModel rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child = _
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      simp only [HedgeWitness.smallCarrierDefectParityModel,
        hedgeCarrierDefectModel]
      rw [oldInputsEq, defectAt]
      rfl
    have baseOutside :
        (w.smallParityModel rich).mechanism child
            (fun parent _edge =>
              (w.smallCarrierDefectParityModel rich).eval u parent)
            (fun root _incident => hedgeDefectOldAssignment G u root) =
          hedgePrivateDecode S child
            ((hedgePrivateCoordinatesOf G
              (hedgeDefectOldAssignment G u)) child) := by
      simp [HedgeWitness.smallParityModel, hedgeNestedForestParityModel,
        hedgeForestParityOutput, outside, inSmall,
        hedgePrivateCoordinatesOf]
    rw [baseOutside] at outputEq
    simp [different, hedgeParityCarrierValue_reconstruct] at outputEq
    exact outputEq.symm

/-- The nested support conditions determine evaluation at every node.  The
outer branch uses the large forest equation, while the inner branch uses the
restricted small forest equation; both recurse only through earlier directed
parents. -/
theorem HedgeWitness.smallCarrierDefectParityModel_evalNode_eq_of_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (u : (w.smallCarrierDefectParityModel rich).latent.Assignment)
    (defectEq : hedgeDefectBitOf G u =
      w.smallCarrierDefectBit rich target)
    (realizes : hedgeNestedPairBitsRealizes G w.large w.small
      (w.smallCarrierDefectIncidence rich target)
      (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) = true)
    (privateFits : hedgeCarrierPrivateCoordinatesFit rich w.large target
      (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G u)) = true)
    (child : Fin S.count) :
    (w.smallCarrierDefectParityModel rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child = target child := by
  have oldInputsEq := hedgeDefectOldInputs_eq_oldAssignment G w.actionRoot
    child u
  have defectAt := hedgeIndependentDefectBit_eq_bitOf G w.actionRoot child u
  have outputEq :
      (w.smallCarrierDefectParityModel rich).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child =
        hedgeParityCarrierValue rich child
          (Bool.xor
            (hedgeIsSecond rich child
              ((w.smallParityModel rich).mechanism child
                (fun parent _edge =>
                  (w.smallCarrierDefectParityModel rich).evalNodeUnder
                    (FiniteLatentSCM.noIntervention S) u parent)
                (fun root _incident =>
                  hedgeDefectOldAssignment G u root)))
            (if child = w.actionRoot then hedgeDefectBitOf G u else false))
          (hedgePrivateDecode S child
            ((hedgePrivateCoordinatesOf G
              (hedgeDefectOldAssignment G u)) child)) := by
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    simp only [HedgeWitness.smallCarrierDefectParityModel,
      hedgeCarrierDefectModel]
    rw [oldInputsEq, defectAt]
    rfl
  cases inLarge : w.large child with
  | false =>
      have inSmall : w.small child = false := by
        cases selected : w.small child
        · rfl
        · have selectedLarge := w.small_subset_large child selected
          rw [inLarge] at selectedLarge
          contradiction
      have different : child ≠ w.actionRoot := by
        intro equal
        subst child
        rw [w.actionRoot_in_large] at inLarge
        contradiction
      have baseOutside :
          (w.smallParityModel rich).mechanism child
              (fun parent _edge =>
                (w.smallCarrierDefectParityModel rich).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent)
              (fun root _incident => hedgeDefectOldAssignment G u root) =
            hedgePrivateDecode S child
              ((hedgePrivateCoordinatesOf G
                (hedgeDefectOldAssignment G u)) child) := by
        simp [HedgeWitness.smallParityModel, hedgeNestedForestParityModel,
          hedgeForestParityOutput, inLarge, inSmall,
          hedgePrivateCoordinatesOf]
      rw [outputEq, baseOutside]
      simp only [different, if_false, Bool.xor_false]
      rw [hedgeParityCarrierValue_reconstruct]
      exact hedgeCarrierPrivateCoordinatesFit_outside rich w.large target
        (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G u))
        privateFits child inLarge
  | true =>
      rw [outputEq]
      refine (congrArg
        (fun bit => hedgeParityCarrierValue rich child bit
          (hedgePrivateDecode S child
            ((hedgePrivateCoordinatesOf G
              (hedgeDefectOldAssignment G u)) child))) ?_).trans
        (hedgeCarrierPrivateCoordinatesFit_inside rich w.large target
          (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G u))
          privateFits child inLarge)
      cases inSmall : w.small child with
      | false =>
          have parentsEq :
              hedgeForestParentBitsFrom rich w.child child
                  (fun parent edge =>
                    (w.smallCarrierDefectParityModel rich).evalNodeUnder
                      (FiniteLatentSCM.noIntervention S) u parent) =
                hedgeForestParentBitsFrom rich w.child child
                  (fun parent _edge => target parent) := by
            exact hedgeForestParentBitsFrom_congr rich child
              (fun _parent => rfl)
              (fun parent edge =>
                w.smallCarrierDefectParityModel_evalNode_eq_of_support rich
                  target u defectEq realizes privateFits parent)
          have nestedPairEq := hedgeNestedPairBitsRealizes_spec G w.large
            w.small (w.smallCarrierDefectIncidence rich target)
            (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) realizes child
            inLarge
          have pairEq :
              hedgeXorPairBitsWithin G w.large child
                  (fun root _incident => hedgeDefectOldAssignment G u root) =
                w.smallCarrierDefectIncidence rich target child := by
            rw [hedgeXorPairBitsWithin_pairBitsOf]
            simpa [hedgeNestedXorPairBitsWithinFrom, inSmall] using
              nestedPairEq
          have largeBase := hedgeForestParityOutput_bit_of_mem G rich w.large
            w.child child
            (fun parent edge =>
              (w.smallCarrierDefectParityModel rich).evalNodeUnder
                (FiniteLatentSCM.noIntervention S) u parent)
            (fun root _incident => hedgeDefectOldAssignment G u root) inLarge
          have baseBit :
              hedgeIsSecond rich child
                  ((w.smallParityModel rich).mechanism child
                    (fun parent edge =>
                      (w.smallCarrierDefectParityModel rich).evalNodeUnder
                        (FiniteLatentSCM.noIntervention S) u parent)
                    (fun root _incident =>
                      hedgeDefectOldAssignment G u root)) =
                Bool.xor
                  (hedgeXorPairBitsWithin G w.large child
                    (fun root _incident => hedgeDefectOldAssignment G u root))
                  (hedgeForestParentBitsFrom rich w.child child
                    (fun parent edge =>
                      (w.smallCarrierDefectParityModel rich).evalNodeUnder
                        (FiniteLatentSCM.noIntervention S) u parent)) := by
            rw [← w.parityMechanism_eq_of_not_small rich child _ _ inSmall]
            exact largeBase
          rw [baseBit, pairEq, parentsEq, defectEq]
          unfold HedgeWitness.smallCarrierDefectIncidence
            hedgeDefectAdjustedTarget HedgeWitness.smallCarrierDefectBit
            hedgeNestedForestRequiredIncidence hedgeForestRequiredIncidence
          simp only [inSmall, Bool.false_eq_true, if_false]
          have different : child ≠ w.actionRoot := by
            intro equal
            subst child
            rw [w.actionRoot_in_small] at inSmall
            contradiction
          simp only [different, if_false]
          generalize hedgeIsSecond rich child (target child) = output
          generalize hedgeForestParentBitsFrom rich w.child child
            (fun parent _edge => target parent) = parents
          cases output <;> cases parents <;> rfl
      | true =>
          let smallKept := restrictChild w.small w.child
          have parentsEq :
              hedgeForestParentBitsFrom rich smallKept child
                  (fun parent edge =>
                    (w.smallCarrierDefectParityModel rich).evalNodeUnder
                      (FiniteLatentSCM.noIntervention S) u parent) =
                hedgeForestParentBitsFrom rich smallKept child
                  (fun parent _edge => target parent) := by
            exact hedgeForestParentBitsFrom_congr rich child
              (fun _parent => rfl)
              (fun parent edge =>
                w.smallCarrierDefectParityModel_evalNode_eq_of_support rich
                  target u defectEq realizes privateFits parent)
          have nestedPairEq := hedgeNestedPairBitsRealizes_spec G w.large
            w.small (w.smallCarrierDefectIncidence rich target)
            (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) realizes child
            inLarge
          have pairEq :
              hedgeXorPairBitsWithin G w.small child
                  (fun root _incident => hedgeDefectOldAssignment G u root) =
                w.smallCarrierDefectIncidence rich target child := by
            rw [hedgeXorPairBitsWithin_pairBitsOf]
            simpa [hedgeNestedXorPairBitsWithinFrom, inSmall] using
              nestedPairEq
          have smallBase := hedgeForestParityOutput_bit_of_mem G rich w.small
            smallKept child
            (fun parent edge =>
              (w.smallCarrierDefectParityModel rich).evalNodeUnder
                (FiniteLatentSCM.noIntervention S) u parent)
            (fun root _incident => hedgeDefectOldAssignment G u root) inSmall
          have baseBit :
              hedgeIsSecond rich child
                  ((w.smallParityModel rich).mechanism child
                    (fun parent edge =>
                      (w.smallCarrierDefectParityModel rich).evalNodeUnder
                        (FiniteLatentSCM.noIntervention S) u parent)
                    (fun root _incident =>
                      hedgeDefectOldAssignment G u root)) =
                Bool.xor
                  (hedgeXorPairBitsWithin G w.small child
                    (fun root _incident => hedgeDefectOldAssignment G u root))
                  (hedgeForestParentBitsFrom rich smallKept child
                    (fun parent edge =>
                      (w.smallCarrierDefectParityModel rich).evalNodeUnder
                        (FiniteLatentSCM.noIntervention S) u parent)) := by
            rw [w.smallParityMechanism_of_small rich child _ _ inSmall]
            exact smallBase
          rw [baseBit, pairEq, parentsEq, defectEq]
          have nestedParityEq :
              hedgeNodeXor w.small
                  (hedgeNestedForestRequiredIncidence rich w.small w.child
                    (restrictChild w.small w.child) target) =
                hedgeNodeXor w.small
                  (hedgeForestRequiredIncidence rich
                    (restrictChild w.small w.child) target) := by
            simpa [HedgeWitness.smallCarrierDefectBit] using
              w.smallCarrierDefectBit_eq_inner rich target
          dsimp only [smallKept]
          rw [w.smallCarrierDefectBit_eq_inner rich target]
          unfold HedgeWitness.smallCarrierDefectIncidence
            hedgeDefectAdjustedTarget
          rw [nestedParityEq]
          unfold hedgeNestedForestRequiredIncidence
            hedgeForestRequiredIncidence
          simp only [inSmall, if_true]
          by_cases equal : child = w.actionRoot <;>
            simp only [equal, if_true, if_false]
          all_goals
            generalize hedgeIsSecond rich child (target child) = output
            generalize hedgeForestParentBitsFrom rich
              (restrictChild w.small w.child) child
              (fun parent _edge => target parent) = parents
            generalize hedgeNodeXor w.small (fun node =>
              Bool.xor (hedgeIsSecond rich node (target node))
                (hedgeForestParentBitsFrom rich
                  (restrictChild w.small w.child) node
                  (fun parent _edge => target parent))) = parity
            cases output <;> cases parents <;> cases parity <;> rfl
termination_by child.val
decreasing_by
  all_goals exact S.directed_earlier edge

/-- Complete nested evaluation follows from the three finite support
conditions. -/
theorem HedgeWitness.smallCarrierDefectParityModel_eval_eq_of_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (u : (w.smallCarrierDefectParityModel rich).latent.Assignment)
    (defectEq : hedgeDefectBitOf G u =
      w.smallCarrierDefectBit rich target)
    (realizes : hedgeNestedPairBitsRealizes G w.large w.small
      (w.smallCarrierDefectIncidence rich target)
      (hedgePairBitsOf G (hedgeDefectOldAssignment G u)) = true)
    (privateFits : hedgeCarrierPrivateCoordinatesFit rich w.large target
      (hedgePrivateCoordinatesOf G (hedgeDefectOldAssignment G u)) = true) :
    (w.smallCarrierDefectParityModel rich).eval u = target := by
  funext child
  exact w.smallCarrierDefectParityModel_evalNode_eq_of_support rich target u
    defectEq realizes privateFits child

/-- Nested-carrier evaluation is exactly membership in its finite support
list. -/
theorem HedgeWitness.smallCarrierDefectParityModel_eval_mem_support_iff
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (u : (w.smallCarrierDefectParityModel rich).latent.Assignment) :
    (w.smallCarrierDefectParityModel rich).eval u = target ↔
      u ∈ w.smallCarrierDefectObservationalSupport rich target := by
  change ((root : Fin (hedgeDefectLatentCount G)) →
    hedgeDefectLatentValue G root) at u
  change (w.smallCarrierDefectParityModel rich).eval u = target ↔
    u ∈ hedgeCarrierDefectSupportLatents G rich w.large target
      (hedgeNestedPairBitsRealizes G w.large w.small
        (w.smallCarrierDefectIncidence rich target))
      (w.smallCarrierDefectBit rich target)
  rw [hedgeCarrierDefectSupportLatents_mem_iff,
    hedgeCarrierCoordinateSupportLatents_mem_iff]
  constructor
  · intro evaluates
    subst target
    exact ⟨w.smallCarrierDefectBitOf_eval rich u,
      w.smallCarrierDefectPairBitsRealizes_eval rich u,
      w.smallCarrierPrivateCoordinatesFit_eval rich u⟩
  · intro support
    exact w.smallCarrierDefectParityModel_eval_eq_of_support rich target u
      support.1 support.2.1 support.2.2

/-! ### Equal prior mass on corresponding support points -/

/-- A weighted list contributes zero to a singleton whose label is absent. -/
theorem eventMass_weighted_not_mem
    {Ω : Type _} [DecidableEq Ω] (values : List Ω) (weight : Ω → Nat)
    {chosen : Ω} (notMember : chosen ∉ values) :
    FiniteProbRecord.eventMass
        (values.map fun value => (value, weight value))
        (FiniteProbRecord.singletonEvent chosen) = 0 := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, FiniteProbRecord.eventMass]
      have different : value ≠ chosen := by
        intro equal
        exact notMember (List.mem_cons.mpr (Or.inl equal.symm))
      have headFalse :
          FiniteProbRecord.singletonEvent chosen value = false := by
        simp [FiniteProbRecord.singletonEvent, different]
      have restMissing : chosen ∉ rest := fun member =>
        notMember (List.mem_cons.mpr (Or.inr member))
      rw [headFalse]
      simp only [Bool.false_eq_true, if_false]
      exact inductionHypothesis restMissing

/-- In a duplicate-free weighted enumeration, singleton mass is exactly the
weight of its unique listed occurrence. -/
theorem eventMass_weighted_singleton_eq
    {Ω : Type _} [DecidableEq Ω] (values : List Ω) (weight : Ω → Nat)
    {chosen : Ω} (member : chosen ∈ values) (nodup : values.Nodup) :
    FiniteProbRecord.eventMass
        (values.map fun value => (value, weight value))
        (FiniteProbRecord.singletonEvent chosen) = weight chosen := by
  induction values with
  | nil => cases member
  | cons value rest inductionHypothesis =>
      have parts := List.nodup_cons.mp nodup
      simp only [List.map_cons, FiniteProbRecord.eventMass]
      by_cases equal : value = chosen
      · subst value
        have restZero := eventMass_weighted_not_mem rest weight parts.1
        simp [FiniteProbRecord.singletonEvent, restZero]
      · have inRest : chosen ∈ rest := by
          rcases List.mem_cons.mp member with head | tail
          · exact (equal head.symm).elim
          · exact tail
        have headFalse :
            FiniteProbRecord.singletonEvent chosen value = false := by
          simp [FiniteProbRecord.singletonEvent, equal]
        rw [headFalse]
        simp only [Bool.false_eq_true, if_false]
        exact inductionHypothesis inRest parts.2

/-- The augmented per-coordinate enumeration is duplicate-free. -/
theorem hedgeDefectLatentEnum_nodup (G : ObservedGraph S)
    (root : Fin (hedgeDefectLatentCount G)) :
    (hedgeDefectLatentEnum G root).Nodup := by
  refine Fin.cases
    (motive := fun root => (hedgeDefectLatentEnum G root).Nodup)
    ?_ (fun old => ?_) root
  · exact (nodup_cast_list (hedgeDefectLatentValue_zero G).symm
      [false, true]).mpr (by simp)
  · exact (nodup_cast_list (hedgeDefectLatentValue_succ G old).symm
      (hedgeLatentEnum G old)).mpr (hedgeLatentEnum_nodup G old)

/-- Singleton mass in one augmented factor is its declared coordinate
weight. -/
theorem hedgeDefectLatentFactor_singleton_mass
    (G : ObservedGraph S) (root : Fin (hedgeDefectLatentCount G))
    (value : hedgeDefectLatentValue G root) :
    FiniteProbRecord.eventMass (hedgeDefectLatentFactor G root).atoms
        (FiniteProbRecord.singletonEvent value) =
      hedgeDefectLatentWeight G root value :=
  eventMass_weighted_singleton_eq (hedgeDefectLatentEnum G root)
    (hedgeDefectLatentWeight G root)
    (hedgeDefectLatentEnum_complete G root value)
    (hedgeDefectLatentEnum_nodup G root)

/-- Two augmented assignments with the same distinguished defect have equal
weight at every coordinate.  All successor-coordinate weights are one. -/
theorem hedgeDefectLatentWeight_eq_of_bit (G : ObservedGraph S)
    (left right : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root)
    (sameDefect : hedgeDefectBitOf G left = hedgeDefectBitOf G right)
    (root : Fin (hedgeDefectLatentCount G)) :
    hedgeDefectLatentWeight G root (left root) =
      hedgeDefectLatentWeight G root (right root) := by
  refine Fin.cases
    (motive := fun root =>
      hedgeDefectLatentWeight G root (left root) =
        hedgeDefectLatentWeight G root (right root))
    ?_ (fun old => ?_) root
  · change (if hedgeDefectBitOf G left then 1 else 2) =
      (if hedgeDefectBitOf G right then 1 else 2)
    rw [sameDefect]
  · simp [hedgeDefectLatentWeight]

/-- Natural singleton numerator of the augmented product prior, exposed as
the product of its coordinate weights. -/
theorem hedgeDefectPrior_eventMass_singleton (G : ObservedGraph S)
    (u : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) :
    FiniteProbRecord.eventMass (hedgeDefectPrior G).atoms
        (FiniteProbRecord.singletonEvent u) =
      FiniteProduct.natProduct (hedgeDefectLatentCount G) (fun root =>
        hedgeDefectLatentWeight G root (u root)) := by
  rw [← hedgeDefectRectangular_eq_singleton G u]
  change FiniteProbRecord.eventMass
      (FiniteProduct.atoms (hedgeDefectLatentCount G)
        (hedgeDefectLatentValue G) (hedgeDefectLatentFactor G))
      (FiniteProduct.rectangularEvent (hedgeDefectLatentCount G)
        (hedgeDefectLatentValue G)
        (fun root value => decide (value = u root))) = _
  rw [FiniteProduct.eventMass_atoms]
  congr 1
  funext root
  simpa [FiniteProbRecord.singletonEvent] using
    hedgeDefectLatentFactor_singleton_mass G root (u root)

/-- Augmented prior atoms have equivalent probability whenever their defect
bits agree; old pair and private coordinates may differ arbitrarily. -/
theorem hedgeDefectPrior_singleton_equiv_of_bit (G : ObservedGraph S)
    (left right : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root)
    (sameDefect : hedgeDefectBitOf G left = hedgeDefectBitOf G right) :
    QProb.Equiv
      ((hedgeDefectPrior G).probVal
        (FiniteProbRecord.singletonEvent left))
      ((hedgeDefectPrior G).probVal
        (FiniteProbRecord.singletonEvent right)) := by
  simp only [QProb.Equiv, FiniteProbRecord.probVal,
    hedgeDefectPrior_eventMass_singleton]
  apply congrArg (fun numerator => numerator * (hedgeDefectPrior G).den)
  apply congrArg (FiniteProduct.natProduct (hedgeDefectLatentCount G))
  funext root
  exact hedgeDefectLatentWeight_eq_of_bit G left right sameDefect root

/-- Equal-length finite supports have equivalent singleton sums when the
atom comparison is required only on values that actually occur in the two
lists.  This is the weighted analogue of the uniform helper in
`Completeness`; carrying membership hypotheses is essential because the
biased defect prior has two distinct atom weights. -/
theorem FiniteProbRecord.listSum_singletons_equiv_of_length_on
    {Ω : Type} [DecidableEq Ω]
    (leftRecord rightRecord : FiniteProbRecord Ω)
    (leftValues rightValues : List Ω)
    (sameLength : leftValues.length = rightValues.length)
    (atomEquiv : ∀ left, left ∈ leftValues → ∀ right, right ∈ rightValues →
      QProb.Equiv
        (leftRecord.probVal (FiniteProbRecord.singletonEvent left))
        (rightRecord.probVal (FiniteProbRecord.singletonEvent right))) :
    QProb.Equiv
      (QProb.listSum (leftValues.map fun value =>
        leftRecord.probVal (FiniteProbRecord.singletonEvent value)))
      (QProb.listSum (rightValues.map fun value =>
        rightRecord.probVal (FiniteProbRecord.singletonEvent value))) := by
  induction leftValues generalizing rightValues with
  | nil =>
      cases rightValues with
      | nil => exact QProb.equiv_refl QProb.zero
      | cons _head _tail => cases sameLength
  | cons left leftTail inductionHypothesis =>
      cases rightValues with
      | nil => cases sameLength
      | cons right rightTail =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          simp only [List.map_cons, QProb.listSum]
          exact QProb.add_congr
            (atomEquiv left (List.mem_cons_self) right (List.mem_cons_self))
            (inductionHypothesis rightTail sameLength
              (fun leftValue leftMember rightValue rightMember =>
                atomEquiv leftValue (List.mem_cons_of_mem left leftMember)
                  rightValue (List.mem_cons_of_mem right rightMember)))

/-- Every member of a fixed-defect support has the advertised distinguished
bit. -/
theorem hedgeCarrierDefectSupportLatents_bitOf_of_mem (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (outer : NodeSet S)
    (target : S.Assignment)
    (pairTest : (Fin (pairRootCount G) → Bool) → Bool)
    (defect : Bool)
    {u : (root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root}
    (member : u ∈
      hedgeCarrierDefectSupportLatents G rich outer target pairTest defect) :
    hedgeDefectBitOf G u = defect :=
  (hedgeCarrierDefectSupportLatents_mem_iff G rich outer target pairTest
    defect u).mp member |>.1

/-! ### Observational equivalence of the positive carrier pair -/

/-- Every observed singleton has equivalent probability in the large and
nested positive carrier models.  Exact semantic support turns each probability
into a duplicate-free finite sum.  Equal support length handles the uniform
old coordinates, while `largeCarrierDefectBit_eq_small` ensures that every
summand uses the same side of the biased defect prior. -/
theorem HedgeWitness.carrierDefectParityModels_observational_singleton_equiv
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) :
    QProb.Equiv
      ((w.largeCarrierDefectParityModel rich).observationalValue
        (FiniteProbRecord.singletonEvent target))
      ((w.smallCarrierDefectParityModel rich).observationalValue
        (FiniteProbRecord.singletonEvent target)) := by
  let largeSupport := w.largeCarrierDefectObservationalSupport rich target
  let smallSupport := w.smallCarrierDefectObservationalSupport rich target
  have largeEvalIff
      (u : (w.largeCarrierDefectParityModel rich).latent.Assignment) :
      (w.largeCarrierDefectParityModel rich).eval u = target ↔
        u ∈ largeSupport := by
    simpa [largeSupport] using
      w.largeCarrierDefectParityModel_eval_mem_support_iff rich target u
  have smallEvalIff
      (u : (w.smallCarrierDefectParityModel rich).latent.Assignment) :
      (w.smallCarrierDefectParityModel rich).eval u = target ↔
        u ∈ smallSupport := by
    simpa [smallSupport] using
      w.smallCarrierDefectParityModel_eval_mem_support_iff rich target u
  have largeEvent
      (u : (w.largeCarrierDefectParityModel rich).latent.Assignment) :
      FiniteProbRecord.singletonEvent target
          ((w.largeCarrierDefectParityModel rich).eval u) =
        FiniteProbRecord.membershipEvent largeSupport u := by
    apply Bool.eq_iff_iff.mpr
    simpa only [FiniteProbRecord.singletonEvent,
      FiniteProbRecord.membershipEvent, decide_eq_true_eq] using largeEvalIff u
  have smallEvent
      (u : (w.smallCarrierDefectParityModel rich).latent.Assignment) :
      FiniteProbRecord.singletonEvent target
          ((w.smallCarrierDefectParityModel rich).eval u) =
        FiniteProbRecord.membershipEvent smallSupport u := by
    apply Bool.eq_iff_iff.mpr
    simpa only [FiniteProbRecord.singletonEvent,
      FiniteProbRecord.membershipEvent, decide_eq_true_eq] using smallEvalIff u
  have largeMembership :
      QProb.Equiv
        ((w.largeCarrierDefectParityModel rich).prior.probVal fun u =>
          FiniteProbRecord.singletonEvent target
            ((w.largeCarrierDefectParityModel rich).eval u))
        ((w.largeCarrierDefectParityModel rich).prior.probVal
          (FiniteProbRecord.membershipEvent largeSupport)) :=
    (w.largeCarrierDefectParityModel rich).prior.probVal_congr _ _ largeEvent
  have smallMembership :
      QProb.Equiv
        ((w.smallCarrierDefectParityModel rich).prior.probVal fun u =>
          FiniteProbRecord.singletonEvent target
            ((w.smallCarrierDefectParityModel rich).eval u))
        ((w.smallCarrierDefectParityModel rich).prior.probVal
          (FiniteProbRecord.membershipEvent smallSupport)) :=
    (w.smallCarrierDefectParityModel rich).prior.probVal_congr _ _ smallEvent
  have largeSum := FiniteProbRecord.probVal_membership_equiv_listSum
    (w.largeCarrierDefectParityModel rich).prior largeSupport
    (by
      simpa [largeSupport] using
        w.largeCarrierDefectObservationalSupport_nodup rich target)
  have smallSum := FiniteProbRecord.probVal_membership_equiv_listSum
    (w.smallCarrierDefectParityModel rich).prior smallSupport
    (by
      simpa [smallSupport] using
        w.smallCarrierDefectObservationalSupport_nodup rich target)
  have supportLength : largeSupport.length = smallSupport.length := by
    simpa [largeSupport, smallSupport] using
      w.carrierDefectObservationalSupport_length_eq rich target
  have atomEquiv
      (left : (w.largeCarrierDefectParityModel rich).latent.Assignment)
      (leftMember : left ∈ largeSupport)
      (right : (w.smallCarrierDefectParityModel rich).latent.Assignment)
      (rightMember : right ∈ smallSupport) :
      QProb.Equiv
        ((w.largeCarrierDefectParityModel rich).prior.probVal
          (FiniteProbRecord.singletonEvent left))
        ((w.smallCarrierDefectParityModel rich).prior.probVal
          (FiniteProbRecord.singletonEvent right)) := by
    change ((root : Fin (hedgeDefectLatentCount G)) →
      hedgeDefectLatentValue G root) at left right
    have leftBit : hedgeDefectBitOf G left =
        w.largeCarrierDefectBit rich target := by
      apply hedgeCarrierDefectSupportLatents_bitOf_of_mem G rich w.large target
        (hedgePairBitsRealizes G w.large
          (w.largeCarrierDefectIncidence rich target))
        (w.largeCarrierDefectBit rich target)
      simpa [largeSupport,
        HedgeWitness.largeCarrierDefectObservationalSupport,
        HedgeWitness.largeCarrierDefectParityModel, hedgeCarrierDefectModel,
        hedgeDefectLatentExtension] using leftMember
    have rightBit : hedgeDefectBitOf G right =
        w.smallCarrierDefectBit rich target := by
      apply hedgeCarrierDefectSupportLatents_bitOf_of_mem G rich w.large target
        (hedgeNestedPairBitsRealizes G w.large w.small
          (w.smallCarrierDefectIncidence rich target))
        (w.smallCarrierDefectBit rich target)
      simpa [smallSupport,
        HedgeWitness.smallCarrierDefectObservationalSupport,
        HedgeWitness.smallCarrierDefectParityModel, hedgeCarrierDefectModel,
        hedgeDefectLatentExtension] using rightMember
    change QProb.Equiv
      ((hedgeDefectPrior G).probVal
        (FiniteProbRecord.singletonEvent left))
      ((hedgeDefectPrior G).probVal
        (FiniteProbRecord.singletonEvent right))
    exact hedgeDefectPrior_singleton_equiv_of_bit G left right
      (leftBit.trans
        ((w.largeCarrierDefectBit_eq_small rich target).trans rightBit.symm))
  have equalSums :=
    FiniteProbRecord.listSum_singletons_equiv_of_length_on
      (w.largeCarrierDefectParityModel rich).prior
      (w.smallCarrierDefectParityModel rich).prior
      largeSupport smallSupport supportLength atomEquiv
  exact QProb.equiv_trans
    ((w.largeCarrierDefectParityModel rich).observationalValue_eq
      (FiniteProbRecord.singletonEvent target))
    (QProb.equiv_trans largeMembership
      (QProb.equiv_trans largeSum
        (QProb.equiv_trans equalSums
          (QProb.equiv_trans (QProb.equiv_symm smallSum)
            (QProb.equiv_trans (QProb.equiv_symm smallMembership)
              (QProb.equiv_symm
                ((w.smallCarrierDefectParityModel rich).observationalValue_eq
                  (FiniteProbRecord.singletonEvent target))))))))

/-- The two full-support carrier models agree on every observational event. -/
theorem HedgeWitness.carrierDefectParityModels_observationally_equivalent
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S) :
    ObservationallyEquivalent (w.largeCarrierDefectParityModel rich)
      (w.smallCarrierDefectParityModel rich) := by
  intro event
  exact FiniteProbRecord.probVal_extensional_of_singletons
    (w.largeCarrierDefectParityModel rich).observationalDist
    (w.smallCarrierDefectParityModel rich).observationalDist
    S.assignmentEnumeration S.assignmentEnumeration_nodup
    S.assignmentEnumeration_complete
    (w.carrierDefectParityModels_observational_singleton_equiv rich) event

end Causality
end Thesis
