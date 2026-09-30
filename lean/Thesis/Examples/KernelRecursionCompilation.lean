import Thesis.CausalTransport.KernelRecursionCompilation
import Thesis.Examples.ComponentCompilation

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentKernelRecursionCompilation

open Probability
open FrontDoorIdentification
open CurrentKernelCompilation
open CurrentKernelComponentCompilation

/-!
# Composed regression for current-kernel recursive branch certificates

The mediator intervention in the front-door graph adds the nonempty block
`{X}`.  Its containing component is `{X,Y}`; inside that host, uncut ancestral
pruning then removes the local action `{X}` because the directed route to
`Y` passes through the already fixed external mediator.

The certificates below compose exactly these three kinds of operation:
current-input component extraction, ordinary ancestral marginalization, and
action augmentation by reverse rule 3.  Every recursive input is generated
from the initial observational package, and every nested support tree is
checked throughout the positive graph-model class.

This is a composed certificate regression, not a substitute for induction
over arbitrary engine executions.  The general success compiler still must
assemble every branch, especially the multi-component product branch.
-/

/-! ## Generate the actual recursive input distributions -/

/-- Reflexivity, observational positivity, and full-host closure establish
the initial recursive invariants without an external completeness theorem. -/
noncomputable def initialInput :
    PublishedCurrentKernelInput (GraphModelClass.positive graph)
      graph.dSeparationCorrectness NodeSet.full NodeSet.empty :=
  PublishedCurrentKernelInput.observational graph.dSeparationCorrectness (fun member => member.2)

/-- The containing component's current expression is extracted from the
full observational input.  Its outside mediator becomes an external action. -/
noncomputable def containingInput :
    PublishedCurrentKernelInput (GraphModelClass.positive graph)
      graph.dSeparationCorrectness gappedHost
      (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full gappedHost)) :=
  initialInput.component (fun member => member.2) gappedHost_mem_cComponents

/-- The actual uncut ancestry inside `{X,Y}` for outcome `{Y}`.  The
external mediator is not a random host vertex, so the directed route through
it is not an induced-host edge from `X` to `Y`. -/
def keptOutcomeHost : NodeSet signature :=
  graph.ancestralSet gappedHost (GraphMutilation.none signature) (NodeSet.singleton y)

/-- The recursive input after pruning retains the mediator intervention
and marginalizes the extracted current expression, not the original joint. -/
noncomputable def prunedInput :
    PublishedCurrentKernelInput (GraphModelClass.positive graph)
      graph.dSeparationCorrectness keptOutcomeHost
      (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full gappedHost)) :=
  containingInput.ancestral (fun member => member.2) (NodeSet.singleton y)

/-- The target syntax displays both recursive input operations in order. -/
theorem prunedInput_formula : prunedInput.certificate.formula =
    .marginalize (NodeSet.diff gappedHost keptOutcomeHost)
      (chainProductFrom NodeSet.full (observationalJointTerm signature) gappedHost) := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The local action disappears under *uncut* host ancestry.  Boolean
emptiness checks avoid classical equality decisions on function-valued sets. -/
theorem localAction_after_pruning_empty :
    NodeSet.inter (NodeSet.singleton x) keptOutcomeHost = NodeSet.empty := by
  apply NodeSet.eq_empty_of_isEmpty
  decide +kernel

/-- A selected outcome is its own ancestor, so it remains in the pruned
host without requiring a nonempty-host representative. -/
theorem outcomeSubsetKept : NodeSet.Subset (NodeSet.singleton y) keptOutcomeHost := by
  intro node selected
  exact ancestralSet_contains_targets graph gappedHost (GraphMutilation.none signature)
    (NodeSet.singleton y)
    (NodeSet.singleton_subset_of_mem (by decide : gappedHost y = true) node selected) selected

/-! ## Compile the nested empty-action query and transport it through pruning -/

/-- The final nested call has no local action and marginalizes its actual
current input.  The explicit outer marginal is retained even when its node
selection is empty, consistently with the engine's output convention. -/
noncomputable def nestedOutcomeCertificate :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness
      (.kernel ⟨NodeSet.singleton y,
        NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full gappedHost), NodeSet.empty⟩) :=
  currentKernelMarginalPublishedCertificate (C := GraphModelClass.positive graph)
    graph.dSeparationCorrectness (fun member => member.2)
    keptOutcomeHost (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full gappedHost))
    (NodeSet.singleton y) prunedInput.closed.action_disjoint outcomeSubsetKept prunedInput.certificate

/-- Pruning transports that nested certificate back to the local `{X}`
intervention in the containing component.  Its rule-3 condition comes from
the general host theorem, not from a supplied finite separation test. -/
noncomputable def localActionCertificate :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness
      (.kernel ⟨NodeSet.singleton y,
        NodeSet.union (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full gappedHost))
          (NodeSet.singleton x), NodeSet.empty⟩) :=
  currentKernelPrunePublishedCertificate containingInput (fun member => member.2)
    (NodeSet.singleton x) (NodeSet.singleton y)
    (NodeSet.singleton_subset_of_mem (by decide : gappedHost x = true))
    (NodeSet.singleton_subset_of_mem (by decide : gappedHost y = true))
    (NodeSet.disjoint_singletons_of_ne (by decide))
    (nestedOutcomeCertificate.reindex
      (by
        have emptyAction := localAction_after_pruning_empty
        unfold keptOutcomeHost at emptyAction
        rw [emptyAction, NodeSet.union_empty_right]) rfl)

/-! ## Match the computed extra action and finish the parent query -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The component's external action is exactly the mediator.  The finite
Boolean set equality is converted constructively to function equality. -/
theorem containing_external_action_eq_mediator :
    NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full gappedHost) =
      NodeSet.singleton mediator := by
  apply (NodeSet.equal_eq_true_iff _ _).mp
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The incoming-cut ancestry test really adds the nonempty block `{X}`.
This is separate from the uncut pruning computation above. -/
theorem additional_action_eq_x :
    identificationAdditionalAction graph NodeSet.full mediatorQuery.outcome mediatorQuery.action =
      NodeSet.singleton x := by
  apply (NodeSet.equal_eq_true_iff _ _).mp
  decide +kernel

/-- The parent local action after the nonempty augmentation step. -/
def augmentedLocalAction : NodeSet signature :=
  NodeSet.union mediatorQuery.action (NodeSet.singleton x)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Inside the containing component, the augmented local action retains
exactly `X`; the mediator belongs to the explicit external action instead. -/
theorem augmented_action_inside_component_eq_x :
    NodeSet.inter augmentedLocalAction gappedHost = NodeSet.singleton x := by
  apply (NodeSet.equal_eq_true_iff _ _).mp
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Every host vertex discarded by this component restriction was already
an action of the augmented parent query.  The constructive Boolean subset
test checks the exact premise of the general restriction constructor. -/
theorem discarded_component_vertices_already_action :
    NodeSet.Subset (NodeSet.diff NodeSet.full gappedHost) augmentedLocalAction := by
  apply (NodeSet.subsetBool_eq_true_iff _ _).mp
  decide +kernel

/-- Return from the containing-component query to the augmented full-host
query by the general action reindexing constructor.  No new rule-3 deletion
is inserted here: the two external/local splits describe the same action. -/
noncomputable def containingQueryCertificate :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness
      (.kernel ⟨NodeSet.singleton y, NodeSet.union NodeSet.empty augmentedLocalAction,
        NodeSet.empty⟩) :=
  currentKernelRestrictionPublishedCertificate NodeSet.full gappedHost NodeSet.empty
    augmentedLocalAction (NodeSet.singleton y) (fun _ _ => rfl)
    discarded_component_vertices_already_action
    (localActionCertificate.reindex
      (by rw [augmented_action_inside_component_eq_x]) rfl)

/-- An action-free observational formula for the mediator query obtained
by composed recursive branch certificates.  Reverse rule 3 adds the actual
extra action, and the nested certificate already incorporates extraction
and pruning with their support-preserving input transformations. -/
noncomputable def mediatorRecursiveCertificate :
    PublishedIdentificationCertificate (GraphModelClass.positive graph)
      graph.dSeparationCorrectness mediatorQuery.sourceTerm := by
  let nested := containingQueryCertificate.reindex
    (show ProbabilityTerm.kernel ⟨NodeSet.inter mediatorQuery.outcome NodeSet.full,
        NodeSet.union NodeSet.empty
          (NodeSet.union (NodeSet.inter mediatorQuery.action NodeSet.full)
            (identificationAdditionalAction graph NodeSet.full mediatorQuery.outcome
              mediatorQuery.action)), NodeSet.empty⟩ =
        .kernel ⟨NodeSet.singleton y, NodeSet.union NodeSet.empty augmentedLocalAction,
          NodeSet.empty⟩ by
      rw [NodeSet.inter_full_right, NodeSet.inter_full_right, NodeSet.union_empty_left,
        additional_action_eq_x, NodeSet.union_empty_left]
      rfl) rfl
  let augmented := currentKernelAdditionalActionPublishedCertificate initialInput
    (fun member => member.2) mediatorQuery.action mediatorQuery.outcome
    (by rw [NodeSet.inter_full_right, NodeSet.inter_full_right]
        exact mediatorQuery.action_outcome_disjoint) nested
  exact augmented.reindex
    (by rw [NodeSet.inter_full_right, NodeSet.inter_full_right, NodeSet.union_empty_left]
        rfl) rfl

/-- The complete expression is the nested marginal of the extracted
current-input component product.  None of the transport steps resets it
to a freshly chosen observational distribution. -/
theorem mediatorRecursiveCertificate_formula : mediatorRecursiveCertificate.formula =
    .marginalize (NodeSet.diff keptOutcomeHost (NodeSet.singleton y))
      (.marginalize (NodeSet.diff gappedHost keptOutcomeHost)
        (chainProductFrom NodeSet.full (observationalJointTerm signature) gappedHost)) := rfl

/-- Interpret every composed rule and support node in every positive
compatible model.  Unlike the earlier numerical mediator regression, this
checks the source/formula equality at all assignments throughout the class. -/
noncomputable def mediatorRecursiveCertificate_soundAt
    (model : ExactModel signature) (member : (GraphModelClass.positive graph).Mem model)
    (reference : signature.Assignment) :
    ProbabilityTerm.EquivalentAt model mediatorQuery.sourceTerm
      mediatorRecursiveCertificate.formula reference :=
  let certificate := mediatorRecursiveCertificate.compile
  DoCalculusDerivation.denotational_soundAt
    (graph.publishedSoundness.primitive model member.1) certificate.derivation
    (certificate.supported model member reference
      (member.2.kernelPositiveSupportedValue
        ⟨mediatorQuery.outcome, mediatorQuery.action, NodeSet.empty⟩ reference).toSupported)

end CurrentKernelRecursionCompilation
end Examples
end Causality
end Thesis
