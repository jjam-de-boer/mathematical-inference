import Thesis.CausalTransport.ComponentCompilation
import Thesis.CausalTransport.KernelRecursionSeparation

namespace Thesis
namespace Causality

open Probability

/-!
# Supported recursive steps of current-kernel ID

The recursion carries a certified current expression, its everywhere-positive
support invariant, and parent closure of the random host relative to its
external actions.  The input package below records these invariants together:
the initial observational input establishes them, uncut ancestral restriction
preserves them by marginalization, and c-component restriction preserves them
by the graph-derived extraction compiler.

The two rule-3 branch constructors then transport a nested query certificate
back to its parent query.  Pruning deletes actions outside the uncut outcome
ancestry.  Augmentation uses the reverse of a deletion to add free vertices
outside incoming-cut ancestry.  Their different input operations remain
visible: only pruning marginalizes the current expression.

These are generic induction steps, not a bounded collection of branch-name
stacks.  A complete success compiler must still apply them to every branch
of `identifyKernelFuel`, including the c-component product branch.  No
published completeness or soundness implementation is imported here.
-/

/-! ## The recursive current-expression invariant -/

/-- The supported state consumed by a current-kernel ID invocation.

The expression is `certificate.formula`, not an assumed observational
marginal of `remaining`.  The certified source retains all external actions.
Positivity concerns the actual target expression at every assignment, so
new prefix quotients can be constructed without invoking soundness. -/
structure PublishedCurrentKernelInput
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (remaining externalAction : NodeSet S) where
  closed : G.KernelHostClosed remaining externalAction
  certificate : PublishedIdentificationCertificate C correct
    (.kernel ⟨remaining, externalAction, NodeSet.empty⟩)
  positive : forall (model : ExactModel S), C.Mem model -> forall reference,
    ProbabilityResult.PositiveSupportedValue (certificate.formula.denote model reference)

/-- The initial full observational current expression requires no assumed
identification theorem.  Its certificate is reflexive, its positivity is
the selected model class's regularity condition, and full-host parent
closure is unconditional. -/
noncomputable def PublishedCurrentKernelInput.observational
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model) :
    PublishedCurrentKernelInput C correct NodeSet.full NodeSet.empty where
  closed := ObservedGraph.KernelHostClosed.full G
  certificate := PublishedIdentificationCertificate.refl (observationalJointTerm S)
    (observationalJointTerm_actionFree S)
  positive := fun _model member reference =>
    (obsPositive member).kernelPositiveSupportedValue
      ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩ reference

/-- Uncut ancestral pruning marginalizes the actual current expression
and keeps external actions fixed.  No action-augmentation operation is
hidden in this input transformation.  Parent closure is preserved by the
uncut ancestry theorem, and finite summation preserves strict positivity. -/
noncomputable def PublishedCurrentKernelInput.ancestral
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (outcome : NodeSet S) :
    PublishedCurrentKernelInput C correct
      (G.ancestralSet remaining (GraphMutilation.none S) outcome) externalAction := by
  let kept := G.ancestralSet remaining (GraphMutilation.none S) outcome
  let certificate := currentKernelMarginalPublishedCertificate correct obsPositive
    remaining externalAction kept input.closed.action_disjoint
    (ancestralSet_subset G remaining (GraphMutilation.none S) outcome) input.certificate
  exact {
    closed := input.closed.ancestral outcome
    certificate := certificate
    positive := fun model member reference =>
      ProbabilityTerm.marginalizePositiveSupportedValue model
        (NodeSet.diff remaining kept) input.certificate.formula reference
        (input.positive model member)
  }

/-- The ancestral input transformation keeps precisely the complementary
marginal used by the engine, including an empty complementary selection. -/
theorem PublishedCurrentKernelInput.ancestral_formula
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (outcome : NodeSet S) :
    (input.ancestral obsPositive outcome).certificate.formula =
      .marginalize
        (NodeSet.diff remaining (G.ancestralSet remaining (GraphMutilation.none S) outcome))
        input.certificate.formula := rfl

/-- Component restriction changes the random host and fixes its discarded
vertices.  Its expression is the exact current-input component product;
both parent closure and positive support are established, not assumed for
the next invocation. -/
noncomputable def PublishedCurrentKernelInput.component
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining) :
    PublishedCurrentKernelInput C correct component
      (NodeSet.union externalAction (NodeSet.diff remaining component)) :=
  let compiled := PublishedCurrentKernelComponentCompilation.ofComponent correct obsPositive
    remaining externalAction input.closed listed input.certificate input.positive
  ⟨input.closed.restrict component (cComponents_subset G remaining listed),
    compiled.certificate, compiled.positive⟩

/-- Component restriction retains the original host in each prefix
quotient and selects only the component's factors for the product. -/
theorem PublishedCurrentKernelInput.component_formula
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    {component : NodeSet S} (listed : component ∈ G.cComponents remaining) :
    (input.component obsPositive listed).certificate.formula =
      chainProductFrom remaining input.certificate.formula component := rfl

/-! ## Ordinary ancestral pruning transports the nested query -/

/-- Remove exactly the local actions outside uncut outcome ancestry and
then use the nested certificate.

The nested input distribution is supplied by `PublishedCurrentKernelInput.ancestral`;
this constructor handles the distinct query transformation by rule 3.
The nested formula is returned unchanged, so arbitrary further recursion
is allowed rather than requiring a particular observational target syntax. -/
noncomputable def currentKernelPrunePublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    (nested : PublishedIdentificationCertificate C correct
      (.kernel ⟨outcome, NodeSet.union externalAction
        (NodeSet.inter action (G.ancestralSet remaining (GraphMutilation.none S) outcome)),
        NodeSet.empty⟩)) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨outcome, NodeSet.union externalAction action, NodeSet.empty⟩) := by
  let kept := G.ancestralSet remaining (GraphMutilation.none S) outcome
  let keptAction := NodeSet.inter action kept
  let removed := NodeSet.diff action kept
  let baseAction := NodeSet.union externalAction keptAction
  have keptActionSubset : NodeSet.Subset keptAction action := NodeSet.inter_subset_left _ _
  have removedSubset := (NodeSet.diff_subset_left action kept).trans actionSubset
  have sideDisjoint : FourWayDisjoint baseAction outcome removed NodeSet.empty :=
    FourWayDisjoint.of_empty_w baseAction outcome removed
      (NodeSet.disjoint_union_left_of
        (NodeSet.disjoint_of_subset_right input.closed.action_disjoint outcomeSubset)
        (NodeSet.Disjoint.of_subset_left disjoint keptActionSubset))
      (NodeSet.disjoint_union_left_of
        (NodeSet.disjoint_of_subset_right input.closed.action_disjoint removedSubset)
        (NodeSet.disjoint_inter_diff action kept))
      (NodeSet.disjoint_of_subset_right disjoint.symm (NodeSet.diff_subset_left action kept))
  let deleted := PublishedIdentificationCertificate.prependDoRuleOfPositive obsPositive
    (DoRuleApplication.rule3 (G := G) (separation := pathRuleSeparation G)
      baseAction outcome removed NodeSet.empty sideDisjoint
      (G.pathDSeparated_rule3_prune_actions remaining externalAction action outcome
        input.closed actionSubset outcomeSubset)) nested
  exact deleted.reindex
    (show ProbabilityTerm.kernel ⟨outcome, NodeSet.union externalAction action, NodeSet.empty⟩ =
        .kernel (rule3Left baseAction outcome removed NodeSet.empty) by
      simp only [rule3Left, baseAction, keptAction, removed, NodeSet.union_assoc,
        NodeSet.union_inter_diff]) rfl

/-- Ancestral pruning preserves the nested result's exact target syntax. -/
theorem currentKernelPrunePublishedCertificate_formula
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    (nested : PublishedIdentificationCertificate C correct
      (.kernel ⟨outcome, NodeSet.union externalAction
        (NodeSet.inter action (G.ancestralSet remaining (GraphMutilation.none S) outcome)),
        NodeSet.empty⟩)) :
    (currentKernelPrunePublishedCertificate input obsPositive action outcome
      actionSubset outcomeSubset disjoint nested).formula = nested.formula := rfl

/-! ## Incoming-cut action augmentation keeps the current input unchanged -/

/-- Add the engine's exact incoming-cut non-ancestor block by reversing
rule 3, then apply an arbitrary nested certificate.

The host and current input are unchanged in this branch.  Only the query
action is enlarged; confusing this step with ancestral pruning would lose
the semantics of the replacement algorithm.  The extra action misses both
the existing local action and the outcome by proved finite graph facts. -/
noncomputable def currentKernelAdditionalActionPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (action outcome : NodeSet S)
    (disjoint : NodeSet.Disjoint (NodeSet.inter action remaining) (NodeSet.inter outcome remaining))
    (nested : PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.inter outcome remaining,
        NodeSet.union externalAction
          (NodeSet.union (NodeSet.inter action remaining)
            (identificationAdditionalAction G remaining outcome action)), NodeSet.empty⟩)) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.inter outcome remaining,
        NodeSet.union externalAction (NodeSet.inter action remaining), NodeSet.empty⟩) := by
  let localAction := NodeSet.inter action remaining
  let localOutcome := NodeSet.inter outcome remaining
  let additional := identificationAdditionalAction G remaining outcome action
  let baseAction := NodeSet.union externalAction localAction
  have additionalSubset := identificationAdditionalAction_subset_remaining G remaining outcome action
  have sideDisjoint : FourWayDisjoint baseAction localOutcome additional NodeSet.empty :=
    FourWayDisjoint.of_empty_w baseAction localOutcome additional
      (NodeSet.disjoint_union_left_of
        (NodeSet.disjoint_of_subset_right input.closed.action_disjoint (NodeSet.inter_subset_right _ _))
        disjoint)
      (NodeSet.disjoint_union_left_of
        (NodeSet.disjoint_of_subset_right input.closed.action_disjoint additionalSubset)
        (identificationAdditionalAction_disjoint_action G remaining outcome action).symm)
      (identificationAdditionalAction_disjoint_outcome G remaining outcome action).symm
  let nestedRuleKernel := nested.reindex
    (show ProbabilityTerm.kernel (rule3Left baseAction localOutcome additional NodeSet.empty) =
        .kernel ⟨localOutcome, NodeSet.union externalAction (NodeSet.union localAction additional),
          NodeSet.empty⟩ by simp only [rule3Left, baseAction, NodeSet.union_assoc]) rfl
  exact PublishedIdentificationCertificate.prependSymmetricDoRuleOfPositive obsPositive
    (DoRuleApplication.rule3 (G := G) (separation := pathRuleSeparation G)
      baseAction localOutcome additional NodeSet.empty sideDisjoint
      (G.pathDSeparated_rule3_additional_action remaining externalAction action outcome input.closed))
    nestedRuleKernel

/-- Action augmentation changes no target expression returned by its
recursive call; in particular, it introduces no observational marginal. -/
theorem currentKernelAdditionalActionPublishedCertificate_formula
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (action outcome : NodeSet S)
    (disjoint : NodeSet.Disjoint (NodeSet.inter action remaining) (NodeSet.inter outcome remaining))
    (nested : PublishedIdentificationCertificate C correct
      (.kernel ⟨NodeSet.inter outcome remaining,
        NodeSet.union externalAction
          (NodeSet.union (NodeSet.inter action remaining)
            (identificationAdditionalAction G remaining outcome action)), NodeSet.empty⟩)) :
    (currentKernelAdditionalActionPublishedCertificate input obsPositive action outcome
      disjoint nested).formula = nested.formula := rfl

/-! ## Containing-component recursion only reindexes the fixed actions -/

/-- Fixing discarded host vertices and retaining the action inside `kept`
recovers the original local action, provided every discarded vertex was
already an action.  This is exactly the action invariant of a containing-
component branch whose sole free component is contained in `kept`. -/
theorem currentKernelRestrictionAction_eq (remaining kept action : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (discardedAction : NodeSet.Subset (NodeSet.diff remaining kept) action) :
    NodeSet.union (NodeSet.diff remaining kept) (NodeSet.inter action kept) = action := by
  apply NodeSet.eq_of_subset_of_subset
  · exact NodeSet.union_subset discardedAction (NodeSet.inter_subset_left action kept)
  · intro node selected
    cases keptSelected : kept node with
    | true =>
        exact Bool.or_eq_true_iff.mpr
          (Or.inr (Bool.and_eq_true_iff.mpr ⟨selected, keptSelected⟩))
    | false =>
        exact Bool.or_eq_true_iff.mpr
          (Or.inl (Bool.and_eq_true_iff.mpr
            ⟨actionSubset node selected, by simp [keptSelected]⟩))

/-- The actual singleton-free-component branch supplies the discarded-
action invariant.  Its sole listed free component covers every free host
vertex; containment in `kept` therefore leaves only already intervened
vertices outside `kept`.  No new semantic assumption is needed. -/
theorem currentKernelRestrictionDiscardedAction_of_containing
    (G : ObservedGraph S) (remaining action : NodeSet S)
    {freeComponent kept : NodeSet S}
    (partition : G.cComponents (NodeSet.diff remaining (NodeSet.inter action remaining)) =
      [freeComponent])
    (containing : G.containingCComponent remaining freeComponent = some kept) :
    NodeSet.Subset (NodeSet.diff remaining kept) (NodeSet.inter action remaining) := by
  have freeEqual := cComponents_eq_of_singleton G
    (NodeSet.diff remaining (NodeSet.inter action remaining)) partition
  have freeInside := (containingCComponent_spec G remaining freeComponent containing).2
  intro node discarded
  have parts := Bool.and_eq_true_iff.mp discarded
  cases selected : NodeSet.inter action remaining node with
  | true => rfl
  | false =>
      have free : NodeSet.diff remaining (NodeSet.inter action remaining) node = true :=
        Bool.and_eq_true_iff.mpr ⟨parts.1, by simp [selected]⟩
      have componentSelected : freeComponent node = true := by rw [freeEqual]; exact free
      have keptSelected := freeInside node componentSelected
      have excluded := parts.2
      rw [keptSelected] at excluded
      cases excluded

/-- Transport a containing-component recursive certificate without a new
do-rule step.  The discarded vertices are already fixed by the parent
query, so the new external/local action split denotes the *same* kernel.

The recursive current distribution is supplied by `PublishedCurrentKernelInput.component`.
This action reindexing must not be confused with uncut pruning, which deletes
actions by rule 3, or augmentation, which adds interventions by its symmetry. -/
noncomputable def currentKernelRestrictionPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    (remaining kept externalAction action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (discardedAction : NodeSet.Subset (NodeSet.diff remaining kept) action)
    (nested : PublishedIdentificationCertificate C correct
      (.kernel ⟨outcome,
        NodeSet.union (NodeSet.union externalAction (NodeSet.diff remaining kept))
          (NodeSet.inter action kept), NodeSet.empty⟩)) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨outcome, NodeSet.union externalAction action, NodeSet.empty⟩) :=
  nested.reindex
    (by rw [NodeSet.union_assoc,
      currentKernelRestrictionAction_eq remaining kept action actionSubset discardedAction]) rfl

/-- The engine-facing containment wrapper derives the discarded-action
premise directly from the recorded partition and containing-component
search result.  These are ordinary branch guards, not additional separation
or soundness hypotheses. -/
noncomputable def currentKernelRestrictionPublishedCertificate_of_containing
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    (remaining externalAction action outcome : NodeSet S)
    {freeComponent kept : NodeSet S}
    (partition : G.cComponents (NodeSet.diff remaining (NodeSet.inter action remaining)) =
      [freeComponent])
    (containing : G.containingCComponent remaining freeComponent = some kept)
    (nested : PublishedIdentificationCertificate C correct
      (.kernel ⟨outcome,
        NodeSet.union (NodeSet.union externalAction (NodeSet.diff remaining kept))
          (NodeSet.inter (NodeSet.inter action remaining) kept), NodeSet.empty⟩)) :
    PublishedIdentificationCertificate C correct
      (.kernel ⟨outcome, NodeSet.union externalAction (NodeSet.inter action remaining),
        NodeSet.empty⟩) :=
  currentKernelRestrictionPublishedCertificate remaining kept externalAction
    (NodeSet.inter action remaining) outcome (NodeSet.inter_subset_right action remaining)
    (currentKernelRestrictionDiscardedAction_of_containing G remaining action partition containing)
    nested

end Causality
end Thesis
