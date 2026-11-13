import Thesis.CausalTransport.ConditionalFailureFirstContact
import Thesis.Examples.ConditionalFailureIncidenceConnectivity

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureFirstContact

open Probability FiniteBooleanInteraction PathSpecification
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation
open CurrentConditionalFailureSmallPrefixDirection

/-!
# The actual first-conditioned contact closes the genuine outside-Small case

The real hedge has original Small `U,R`, evidence `P` outside Small, and
opaque normalized path `P <- Y`.  The actual complete stopped approach from
`U` ends at its first conditioner `P`, so it supplies exactly the pivot needed
by the general first-contact reduction, rather than an arbitrary retained
conditioner or a later reachable maximizer.

The first combined contact is the same actual `P` row.  The proved singleton
core identifies every normalized head with `P`, and the actual finite outcome
scan also returns `P`.  Thus the connected-head premise is proved for this
genuine normalization, and the universal first-contact theorem supplies the
successful full Small search and positive original-alphabet countermodels.

Only the small original boundary policy is reduced.  The opaque normal-form
search is never evaluated; its window and core identities remain structural
proofs.  This exercises the complete first-contact branch but does not prove
the still-required universal normalized-head/fork-barrier dichotomy.
-/

private theorem source_in_small : witness.small source = true := by decide +kernel

/-- Use the genuine complete boundary approach from original Small `U`.
Its first-conditioner proof is supplied by the exhaustive actual boundary. -/
def approach : FirstConditionedSmallApproach witness := .ofBoundary boundary source source_in_small

/-- The computed first pivot is literally the original outside-Small
conditioner.  No equality involving the opaque normalizer is reduced here. -/
theorem actual_first_pivot : approach.pivot.node = pivot.node := by decide +kernel

/-- The original existing normal form has precisely this computed pivot
type.  No different path or outcome is constructed for the regression. -/
abbrev actualNormal : ConditionalBackdoorPathNormalForm graph query approach.pivot.node := normal

abbrev actualForest : ConditionalCutColliderActivationForest query approach.pivot.node := forest

/-- The general first-contact endpoint agrees with the proved actual
fork-aware approach.  Only that list's data, not normalization search, are
used to identify its real receiving row. -/
theorem actual_contact : approach.incidenceContact boundary actualNormal actualForest = pivotNode := by
  change CurrentConditionalFailureForkApproach.approach.endpoint = pivotNode
  exact CurrentConditionalFailureForkApproach.actual_endpoint

/-- All genuine normalized heads are connected to the actual starting
incidence.  The singleton core proves there is just the true `P` head; the
finite outcome receiver theorem identifies the same row constructively. -/
theorem actual_heads_connected (head : Fin signature.count) (selected : actualNormal.pathHeads head = true) :
    FiniteReachability.Reachable (actualNormal.forkPairIncidence boundary approach.pivot actualForest)
      (actualNormal.forkOutcomeIncidenceRow boundary approach.pivot actualForest) head := by
  have core : normal.smallInteractionRows pivot forest head = true :=
    NodeSet.subset_union_left _ _ head (NodeSet.subset_union_left _ _ head selected)
  rw [actual_core] at core
  have same := (NodeSet.singleton_eq_true_iff pivotNode head).mp core
  change FiniteReachability.Reachable (normal.forkPairIncidence boundary pivot forest)
    (normal.forkOutcomeIncidenceRow boundary pivot forest) head
  rw [same, CurrentConditionalFailureIncidenceDirection.actual_starting_row]
  exact FiniteReachability.Reachable.refl _ pivotNode

/-- Apply the general first-conditioned contact theorem, rather than
the earlier fixture's manually displayed one-edge incidence connection. -/
theorem actual_connection_from_first_contact :
    actualNormal.forkOutcomeReachesSmallTest boundary approach.pivot actualForest signature.count = true :=
  approach.forkOutcomeReachesSmallTest_of_pathHeads_connected boundary actualNormal actualForest actual_heads_connected

/-- Positive original-three-valued countermodels follow from that genuine
first-contact branch, with every original outcome, intervention, conditioner
and independent reserved input retained by the shared semantic constructor. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfForkIncidenceReachability witness rich boundary approach.pivot actualNormal actualForest
    signature.count actual_connection_from_first_contact

theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

end CurrentConditionalFailureFirstContact
end Examples
end Causality
end Thesis
