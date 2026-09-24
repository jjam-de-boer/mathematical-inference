import Thesis.CausalTransport.Soundness
import Thesis.CausalTransport.Completeness

namespace Thesis
namespace Causality

open Probability

/-!
# Positive hedge counterexamples detected through outcome marginals

`Completeness` proves observational equality of the positive hedge mix under
an edge-wise shared-switch condition.  Its composite-cylinder separation
lemma asks every queried outcome to be a direct child of one action seed.
That is stronger than semantic non-identifiability requires: equality of the
full outcome kernel would imply equality of every outcome marginal.

This module performs that reduction constructively.  It imports the finite
marginalization identity from `Soundness`, while keeping the two main theorem
development files independent of one another.  Pointwise `ValueEquivalent`
witnesses are hidden behind `Nonempty`; the marginal proof folds those
inhabited witnesses over the finite assignment enumeration and never chooses
a global witness family.

The resulting leaf permits arbitrary additional query outcomes.  It needs
only one stored outcome seed with odd action-parent parity and an incident
pair-root.  Extra action vertices may be non-sinks provided every edge leaving
the action preserves pair-root incidence.
-/

/-! ## The theorem-level marginal counterexample -/

/--
The positive edge-shared mix pair separates the complete query as soon as it
separates one selected outcome coordinate.  Assuming equality of the complete
kernel, finite marginalization restricts it to `{y}`; the singleton mix lemma
then supplies the contradiction.
-/
def hedgeEdgeSharedMarginalCounterexampleIn
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) {x y : Fin S.count}
    (root : Fin (pairRootCount G))
    (actionSeed : q.action x = true)
    (parentParity : actionParentParity q.action y = true)
    (outcomeSeed : q.outcome y = true)
    (shared : forall parent child,
      q.action parent = true → S.directed parent child = true →
        forall r,
          (hedgeLatentExtension G).incident (hedgePairRoot G r) parent =
            (hedgeLatentExtension G).incident (hedgePairRoot G r) child)
    (incident :
      (hedgeLatentExtension G).incident (hedgePairRoot G root) y = true) :
    CounterexampleIn (GraphModelClass.positive G) q where
  left := hedgeMixModel G rich NodeSet.empty
  right := hedgeMixModel G rich q.action
  left_mem := hedgeMixModel_mem_positive G rich NodeSet.empty
  right_mem := hedgeMixModel_mem_positive G rich q.action
  observationally_equal :=
    hedgeMixModel_observationally_equivalent_of_edge_shared_switch G rich
      q.action shared
  query_separated := by
    intro completeEquivalent
    let singletonOutcome := NodeSet.singleton y
    have singletonSubset : NodeSet.Subset singletonOutcome q.outcome :=
      NodeSet.singleton_subset_of_mem outcomeSeed
    let singletonQuery := q.restrictOutcome singletonOutcome singletonSubset
    have singletonEquivalent :
        singletonQuery.ValueEquivalent
          (hedgeMixModel G rich NodeSet.empty)
          (hedgeMixModel G rich q.action) := by
      exact JointKernelQuery.valueEquivalent_restrictOutcome q
        (hedgeMixModel G rich NodeSet.empty)
        (hedgeMixModel G rich q.action) completeEquivalent singletonOutcome
        singletonSubset
    have singletonSeparated :
        Not
          (singletonQuery.ValueEquivalent
            (hedgeMixModel G rich NodeSet.empty)
            (hedgeMixModel G rich q.action)) := by
      apply hedgeSingletonOutcome_not_valueEquivalent_of_parentParity G rich
        singletonQuery root
      · exact actionSeed
      · exact parentParity
      · simp [singletonQuery, singletonOutcome,
          JointKernelQuery.restrictOutcome, NodeSet.singleton]
      · intro candidate selected
        exact (NodeSet.singleton_eq_true_iff y candidate).mp selected
      · exact incident
    exact singletonSeparated singletonEquivalent

/-! ## Executable readiness and failure-pipeline integration -/

/--
Boolean readiness for the marginal edge-shared leaf.  Unlike
`hedgeWitnessEdgeSharedReady`, it imposes no shape restriction on outcomes
other than odd action-parent parity at the stored seed: unrelated queried
coordinates are removed by finite marginalization before singleton
separation.
-/
def hedgeWitnessMarginalEdgeSharedReady (G : ObservedGraph S)
    (q : JointKernelQuery S) (w : HedgeWitness G q) : Bool :=
  q.action w.actionSeed &&
    (actionParentParity q.action w.outcomeSeed &&
      (actionEdgesSharePairRootSwitchBool G q.action &&
        (List.finRange (pairRootCount G)).any (fun root =>
          (hedgeLatentExtension G).incident (hedgePairRoot G root)
            w.outcomeSeed)))

/--
The earlier all-outcomes edge-shared test is contained in the marginal test.
Its direct edge and unique-parent scan make the selected outcome's parent
parity odd; the outcome-subset requirement is no longer needed after
marginalization.
-/
theorem hedgeWitnessMarginalEdgeSharedReady_of_edgeSharedReady
    (G : ObservedGraph S) (q : JointKernelQuery S) (w : HedgeWitness G q)
    (ready : hedgeWitnessEdgeSharedReady G q w = true) :
    hedgeWitnessMarginalEdgeSharedReady G q w = true := by
  let actionSeed := (Bool.and_eq_true_iff.mp ready).1
  let rest := (Bool.and_eq_true_iff.mp ready).2
  let _outcomes := (Bool.and_eq_true_iff.mp rest).1
  let rest2 := (Bool.and_eq_true_iff.mp rest).2
  let unique := (Bool.and_eq_true_iff.mp rest2).1
  let rest3 := (Bool.and_eq_true_iff.mp rest2).2
  let directed := (Bool.and_eq_true_iff.mp rest3).1
  let rest4 := (Bool.and_eq_true_iff.mp rest3).2
  let shared := (Bool.and_eq_true_iff.mp rest4).1
  let incident := (Bool.and_eq_true_iff.mp rest4).2
  have parity : actionParentParity q.action w.outcomeSeed = true :=
    actionParentParity_eq_true_of_unique q.action directed actionSeed
      (fun parent selected edge =>
        uniqueActionParentAtOutcomesBool_spec unique w.outcomeSeed
          w.outcomeSeed_in_outcome parent selected edge)
  exact Bool.and_eq_true_iff.mpr ⟨actionSeed,
    Bool.and_eq_true_iff.mpr ⟨parity,
      Bool.and_eq_true_iff.mpr ⟨shared, incident⟩⟩⟩

/-- Readiness of a witness packages the generalized positive counterexample. -/
def hedgeEdgeSharedMarginalCounterexampleIn_of_ready
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) (w : HedgeWitness G q)
    (ready : hedgeWitnessMarginalEdgeSharedReady G q w = true) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  let actionSeed := (Bool.and_eq_true_iff.mp ready).1
  let rest := (Bool.and_eq_true_iff.mp ready).2
  let parity := (Bool.and_eq_true_iff.mp rest).1
  let rest2 := (Bool.and_eq_true_iff.mp rest).2
  let shared := (Bool.and_eq_true_iff.mp rest2).1
  let incident := (Bool.and_eq_true_iff.mp rest2).2
  hedgeEdgeSharedMarginalCounterexampleIn G rich q
    (firstIncidentPairRoot G w.outcomeSeed incident) actionSeed parity
    w.outcomeSeed_in_outcome
    (fun _parent _child selected edge root =>
      actionEdgesSharePairRootSwitchBool_hedgeIncident shared selected edge
        root)
    (firstIncidentPairRoot_incident G w.outcomeSeed incident)

/--
Enhanced executable positive counterexample search.  The marginal leaf is
tried first because it strictly relaxes the earlier all-outcomes-child test;
the original search remains the fallback and retains all established bow and
seed-plus-sink cases.
-/
def hedgePositiveCounterexampleIn? (G : ObservedGraph S)
    (rich : ObservedSignature.ValueRich S) (q : JointKernelQuery S)
    (w : HedgeWitness G q) :
    Option (CounterexampleIn (GraphModelClass.positive G) q) :=
  if ready : hedgeWitnessMarginalEdgeSharedReady G q w = true then
    some (hedgeEdgeSharedMarginalCounterexampleIn_of_ready G rich q w ready)
  else
    hedgeCounterexampleIn? G rich q w

theorem hedgePositiveCounterexampleIn?_isSome_iff
    (G : ObservedGraph S) (rich : ObservedSignature.ValueRich S)
    (q : JointKernelQuery S) (w : HedgeWitness G q) :
    (hedgePositiveCounterexampleIn? G rich q w).isSome =
      (hedgeWitnessMarginalEdgeSharedReady G q w ||
        (hedgeCounterexampleIn? G rich q w).isSome) := by
  dsimp [hedgePositiveCounterexampleIn?]
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
