import Thesis.CausalTransport.GuardedIdentificationKernel
import Thesis.CausalTransport.LocalKernelQueryCompilation
import Thesis.CausalTransport.LocalKernelQueryDataAvailability

namespace Thesis
namespace Causality

open Probability

/-!
# Uniform guarded-ID success compilation from recursive local data

This compiler follows the actual fuel-bounded guarded program.  Its input
is a current-kernel reduction together with a constructor for support from
that input's primitive local data.  Its output preserves this arrangement:
the formula is the literal identified expression, and its support tree is
constructed from recursively composed data, not supplied as a premise.

Every successful branch is covered by the same fuel induction.  In the
multi-component branch the computed child outcomes supply the formulas;
successful collection proves their success equations in `Prop`, and the
induction hypothesis constructs their compilations.  Thus no formula or
compilation is selected from a propositional existence witness.  The family
fold retains host order and its guarded quotients, including interleaved
components; no strict-product regrouping at zero cells is used.

This establishes a sufficient local-support boundary, not unconditional
soundness of every successful formula at every zero-containing distribution.
In particular the boundary retains recursively demanded input data and
positive displayed quotient denominators.  Separate factor-level causal
support and factual-overlap fields have been removed by the completion layer.
There is no global positivity premise or assumed semantic-equality leaf.
`GuardedKernelSoundness` supplies interpretation separately, while
`GuardedConditionalSuccessCompilation` integrates the local conditional
promotion/Bayes constructors.  A zero-unrestricted success equivalence is
not a conclusion of either support-qualified compiler.
-/

variable {S : ObservedSignature} {G : ObservedGraph S} {correct : DSeparationCorrectness G}

/-- An actual recursive compilation with its exact successful output
alignment.  Keeping this equality explicit avoids erasing equality nodes
when source coordinates or executable family lookup are reindexed. -/
structure PublishedLocalKernelSuccess (G : ObservedGraph S) (correct : DSeparationCorrectness G)
    (outcome action : NodeSet S) (term : ProbabilityTerm S) where
  compilation : PublishedLocalKernelCompilation G correct outcome action
  formula_eq : compilation.reduction.formula = term

/-- Expose the literal identified term as the compiled formula.  Local
data is unchanged; the support constructor retains the equality wrapper. -/
noncomputable def PublishedLocalKernelSuccess.aligned
    {outcome action : NodeSet S} {term : ProbabilityTerm S}
    (success : PublishedLocalKernelSuccess G correct outcome action term) :
    PublishedLocalKernelCompilation G correct outcome action :=
  success.compilation.reindex term rfl success.formula_eq.symm

theorem PublishedLocalKernelSuccess.aligned_formula
    {outcome action : NodeSet S} {term : ProbabilityTerm S}
    (success : PublishedLocalKernelSuccess G correct outcome action term) :
    success.aligned.reduction.formula = term := rfl

/-! ## Read computed child formulas without propositional selection -/

private def identifiedFormula (outcome : IdentificationOutcome S) : ProbabilityTerm S :=
  match outcome with
  | .identified term => term
  | _ => unitProbabilityTerm S

private theorem identifiedFormula_eq_of_combined
    {α : Type u} (inputs : List α) (run : α → IdentificationOutcome S)
    (assemble : List (ProbabilityTerm S) → ProbabilityTerm S)
    {term : ProbabilityTerm S}
    (result : IdentificationOutcome.combine (inputs.map run) assemble = .identified term)
    {input : α} (listed : input ∈ inputs) :
    run input = .identified (identifiedFormula (run input)) := by
  rcases IdentificationOutcome.combine_eq_identified _ _ result with
    ⟨terms, outcomesEqual, _⟩
  have included : run input ∈ inputs.map run := List.mem_map.mpr ⟨input, listed, rfl⟩
  rw [outcomesEqual] at included
  rcases List.mem_map.mp included with ⟨factor, _, same⟩
  rw [← same]
  rfl

private theorem combinedTerm_eq_identifiedFormulas
    {α : Type u} (inputs : List α) (run : α → IdentificationOutcome S)
    (assemble : List (ProbabilityTerm S) → ProbabilityTerm S)
    {term : ProbabilityTerm S}
    (result : IdentificationOutcome.combine (inputs.map run) assemble = .identified term) :
    term = assemble (inputs.map (fun input => identifiedFormula (run input))) := by
  rcases IdentificationOutcome.combine_eq_identified _ _ result with
    ⟨terms, outcomesEqual, termEqual⟩
  have mapped := congrArg (List.map identifiedFormula) outcomesEqual
  have factorsEqual : inputs.map (fun input => identifiedFormula (run input)) = terms := by
    simp only [List.map_map] at mapped
    change inputs.map (fun input => identifiedFormula (run input)) =
      terms.map (fun factor => factor) at mapped
    exact mapped.trans (List.map_id terms)
  rw [factorsEqual]
  exact termEqual

/-! ## Finite query geometry and the guarded split branch -/

private theorem intersectHost_eq {selected remaining : NodeSet S}
    (subset : NodeSet.Subset selected remaining) : NodeSet.inter selected remaining = selected := by
  rw [NodeSet.inter_comm, NodeSet.inter_eq_of_subset subset]

private theorem outcome_subset_free {remaining action outcome : NodeSet S}
    (subset : NodeSet.Subset outcome remaining) (disjoint : NodeSet.Disjoint action outcome) :
    NodeSet.Subset outcome (NodeSet.diff remaining action) := by
  intro node selected
  exact Bool.and_eq_true_iff.mpr
    ⟨subset node selected, by rw [disjoint.symm node selected]; rfl⟩

private theorem outcome_empty_of_no_components
    (G : ObservedGraph S) (remaining action outcome : NodeSet S)
    (subset : NodeSet.Subset outcome remaining) (disjoint : NodeSet.Disjoint action outcome)
    (partition : G.cComponents (NodeSet.diff remaining action) = []) : outcome = NodeSet.empty := by
  funext node
  cases selected : outcome node with
  | false => rfl
  | true =>
      rcases cComponents_covers G (NodeSet.diff remaining action)
        (outcome_subset_free subset disjoint node selected) with ⟨component, listed, _⟩
      rw [partition] at listed
      cases listed

/-- The split child's original host complement contains the parent local
action.  This is Boolean source alignment, not an algebraic law at zeros. -/
private theorem componentAction_from_free_eq
    (remaining action component : NodeSet S) (actionSubset : NodeSet.Subset action remaining)
    (componentSubset : NodeSet.Subset component (NodeSet.diff remaining action)) :
    NodeSet.union action (NodeSet.diff (NodeSet.diff remaining action) component) =
      NodeSet.diff remaining component := by
  funext node
  have actionInside : action node = true → remaining node = true := actionSubset node
  have componentInside : component node = true →
      (remaining node && !action node) = true := componentSubset node
  cases hostSelected : remaining node <;> cases actionSelected : action node <;>
    cases componentSelected : component node <;> simp_all [NodeSet.union, NodeSet.diff]

private theorem free_outcome_complement_eq (remaining action outcome : NodeSet S) :
    NodeSet.diff (NodeSet.diff remaining action) outcome =
      NodeSet.diff remaining (NodeSet.union outcome action) := by
  funext node
  change ((remaining node && Bool.not (action node)) && Bool.not (outcome node)) =
    (remaining node && Bool.not (outcome node || action node))
  cases remaining node <;> cases action node <;> cases outcome node <;> rfl

/-- Construct the free host from its actual independently compiled children
and then marginalize.  Parent closure is constructed by restriction.  The
family's recursive data, including each child's exact marginal variants,
is composed by `guardedReduction` and `marginal`, never assumed wholesale. -/
noncomputable def localKernelSplitCompilation
    {remaining externalAction : NodeSet S}
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S) (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining) (disjoint : NodeSet.Disjoint action outcome)
    (formulas : NodeSet S → ProbabilityTerm S)
    (nested : forall component, component ∈ G.cComponents (NodeSet.diff remaining action) →
      PublishedLocalKernelCompilation G correct component
        (NodeSet.union externalAction (NodeSet.diff remaining component)))
    (aligned : forall component listed, (nested component listed).reduction.formula = formulas component) :
    PublishedLocalKernelSuccess G correct outcome (NodeSet.union externalAction action)
      (.marginalize (NodeSet.diff remaining (NodeSet.union outcome action))
        (guardedComponentFamilyTerm G (NodeSet.diff remaining action) formulas)) := by
  let free := NodeSet.diff remaining action
  let baseAction := NodeSet.union externalAction action
  have discarded : NodeSet.diff remaining free = action := by
    change NodeSet.diff remaining (NodeSet.diff remaining action) = action
    rw [NodeSet.diff_diff, NodeSet.inter_eq_of_subset actionSubset]
  have freeClosed : G.KernelHostClosed free baseAction := by
    have restricted := closed.restrict free (NodeSet.diff_subset_left remaining action)
    rw [discarded] at restricted
    exact restricted
  let family : PublishedLocalComponentFamily G correct free baseAction := {
    formula := formulas
    compilation := fun component listed => (nested component listed).reindex (formulas component)
      (by
        change ProbabilityTerm.kernel ⟨component,
          NodeSet.union (NodeSet.union externalAction action)
            (NodeSet.diff (NodeSet.diff remaining action) component), NodeSet.empty⟩ = _
        rw [NodeSet.union_assoc, componentAction_from_free_eq remaining action component
          actionSubset (cComponents_subset G free listed)])
      (aligned component listed).symm
    formula_eq := fun _component _listed => rfl
  }
  let whole := family.guardedReduction freeClosed
  let marginal := whole.marginal outcome freeClosed.action_disjoint (outcome_subset_free outcomeSubset disjoint)
  exact ⟨marginal, by
    change ProbabilityTerm.marginalize (NodeSet.diff free outcome)
      (guardedComponentFamilyTerm G free formulas) = _
    rw [free_outcome_complement_eq]⟩

/-! ## Empty free host, including an empty observed signature -/

private noncomputable def emptyOutcomeLocalKernelCompilation
    {remaining externalAction : NodeSet S}
    (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (closed : G.KernelHostClosed remaining externalAction)
    (action : NodeSet S) (actionSubset : NodeSet.Subset action remaining) :
    PublishedLocalKernelSuccess G correct NodeSet.empty (NodeSet.union externalAction action)
      (.marginalize remaining input.reduction.formula) := by
  let marginal := input.marginal NodeSet.empty closed.action_disjoint
    (fun _node selected => by cases selected)
  have removedEqual : NodeSet.diff remaining NodeSet.empty = remaining := by
    funext node
    exact Bool.and_true (remaining node)
  let nested := marginal.reindex (.marginalize remaining input.reduction.formula) rfl
    (by change ProbabilityTerm.marginalize remaining input.reduction.formula =
          .marginalize (NodeSet.diff remaining NodeSet.empty) input.reduction.formula
        rw [removedEqual])
  have four := FourWayDisjoint.of_empty_w externalAction NodeSet.empty action
    (NodeSet.disjoint_empty_right externalAction)
    (NodeSet.disjoint_of_subset_right closed.action_disjoint actionSubset)
    (NodeSet.disjoint_empty_left action)
  let application := DoRuleApplication.rule3 (G := G) (separation := pathRuleSeparation G)
    externalAction NodeSet.empty action NodeSet.empty four
    (PathSpecification.PathDSeparated.of_isEmpty_left G _ NodeSet.empty action
      (NodeSet.union externalAction NodeSet.empty) NodeSet.isEmpty_empty)
  exact ⟨PublishedLocalKernelCompilation.prependDeleteActions externalAction NodeSet.empty action application nested, rfl⟩

/-! ## All successful recursive invocations, by actual fuel induction -/

/-- Compile the actual identified guarded expression for every fuel and
well-formed recursive query.  The input expression and its inherited data
survive ancestral restriction, component restriction and action changes.
No model class, global positivity, semantic identifiability assumption, or
caller-supplied whole derivation-support tree is an argument. -/
noncomputable def identifyGuardedKernelFuelLocalCompilation
    (fuel : Nat) {remaining externalAction : NodeSet S}
    (input : PublishedLocalKernelCompilation G correct remaining externalAction)
    (closed : G.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet S) (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining) (disjoint : NodeSet.Disjoint action outcome)
    {term : ProbabilityTerm S}
    (result : identifyGuardedKernelFuel fuel G remaining outcome action input.reduction.formula = .identified term) :
    PublishedLocalKernelSuccess G correct outcome (NodeSet.union externalAction action) term := by
  induction fuel generalizing remaining externalAction action outcome term with
  | zero => cases result
  | succ fuel inductionHypothesis =>
      have localAction := intersectHost_eq actionSubset
      have localOutcome := intersectHost_eq outcomeSubset
      simp only [identifyGuardedKernelFuel, localAction, localOutcome] at result
      split at result
      · rename_i emptyAction
        -- Empty local action leaves only the inherited external actions.
        -- Summation asks for the input's own data at its actual variants.
        have actionEmpty := NodeSet.eq_empty_of_isEmpty emptyAction
        cases result
        let marginal := input.marginal outcome closed.action_disjoint outcomeSubset
        exact ⟨marginal.reindex marginal.reduction.formula
          (by rw [actionEmpty, NodeSet.union_empty_right]) rfl, rfl⟩
      · split at result
        · split at result
          · split at result
            · rename_i noComponents
              -- Coverage forces an empty outcome.  Even this degenerate
              -- branch keeps the displayed current-input marginal.
              have emptyOutcome := outcome_empty_of_no_components G remaining action outcome
                outcomeSubset disjoint noComponents
              cases result
              subst outcome
              exact emptyOutcomeLocalKernelCompilation input closed action actionSubset
            · rename_i component oneComponent
              have componentEqual := cComponents_eq_of_singleton G (NodeSet.diff remaining action) oneComponent
              have outcomeInComponent : NodeSet.Subset outcome component := by
                rw [componentEqual]
                exact outcome_subset_free outcomeSubset disjoint
              split at result
              · cases result
              · split at result
                · rename_i componentListed
                  -- Terminal extraction fixes exactly the original local
                  -- actions; unfold the named component action to align it.
                  have listed : component ∈ G.cComponents remaining := by
                    rcases List.any_eq_true.mp componentListed with ⟨piece, included, equal⟩
                    exact ((NodeSet.equal_eq_true_iff piece component).mp equal) ▸ included
                  have discardedEqual : NodeSet.diff remaining component = action := by
                    rw [componentEqual, NodeSet.diff_diff, NodeSet.inter_eq_of_subset actionSubset]
                  cases result
                  let componentInput := input.ofComponent closed listed
                  let componentClosed := closed.restrict component (cComponents_subset G remaining listed)
                  let marginal := componentInput.marginal outcome componentClosed.action_disjoint outcomeInComponent
                  exact ⟨marginal.reindex marginal.reduction.formula
                    (by simp only [componentExternalAction, discardedEqual]) rfl, rfl⟩
                · split at result
                  · rename_i larger containing
                    -- Restrict the current input before recursion.  The
                    -- discarded vertices were actions already, so query
                    -- transport changes their split rather than their value.
                    have specification := containingCComponent_spec G remaining component containing
                    let componentInput := input.ofComponent closed specification.1
                    let componentClosed := closed.restrict larger (cComponents_subset G remaining specification.1)
                    let nested := inductionHypothesis componentInput componentClosed
                      (NodeSet.inter action larger) outcome (NodeSet.inter_subset_right _ _)
                      (outcomeInComponent.trans specification.2)
                      (NodeSet.Disjoint.of_subset_left disjoint (NodeSet.inter_subset_left _ _)) result
                    have discarded : NodeSet.Subset (NodeSet.diff remaining larger) action := by
                      have obtained := currentKernelRestrictionDiscardedAction_of_containing G
                        remaining action (by simpa only [localAction] using oneComponent) containing
                      simpa only [localAction] using obtained
                    exact ⟨localKernelRestrictionCompilation remaining larger externalAction action outcome
                      actionSubset discarded nested.compilation, nested.formula_eq⟩
                  · cases result
            · let run := fun component => identifyGuardedKernelFuel fuel G remaining component
                (NodeSet.diff remaining component) input.reduction.formula
              let formulas := fun component => identifiedFormula (run component)
              -- Formulas are read from computed outcomes; only their success
              -- equations are obtained from the successful collector in Prop.
              let nested := fun component (listed : component ∈ G.cComponents (NodeSet.diff remaining action)) =>
                inductionHypothesis input closed (NodeSet.diff remaining component) component
                  (NodeSet.diff_subset_left _ _)
                  ((cComponents_subset G _ listed).trans (NodeSet.diff_subset_left _ _))
                  (NodeSet.disjoint_diff_right _ _)
                  (identifiedFormula_eq_of_combined _ run _ result listed)
              let compiled := localKernelSplitCompilation closed action outcome actionSubset outcomeSubset disjoint formulas
                (fun component listed => (nested component listed).compilation)
                (fun component listed => (nested component listed).formula_eq)
              have termAlignment := combinedTerm_eq_identifiedFormulas _ run _ result
              rw [assembleGuardedComponents_map] at termAlignment
              exact ⟨compiled.compilation, compiled.formula_eq.trans termAlignment.symm⟩
          · let additional := identificationAdditionalAction G remaining outcome action
            -- Additional incoming-cut actions leave the current expression
            -- unchanged; reverse rule 3 only transports the nested query.
            have additionalSubset := identificationAdditionalAction_subset_remaining G remaining outcome action
            have additionalDisjoint := identificationAdditionalAction_disjoint_outcome G remaining outcome action
            have additionalOutcome : NodeSet.Disjoint additional outcome := by
              simpa only [localOutcome] using additionalDisjoint
            let nested := inductionHypothesis input closed (NodeSet.union action additional) outcome
              (NodeSet.union_subset actionSubset additionalSubset) outcomeSubset
              (NodeSet.disjoint_union_left_of disjoint additionalOutcome) result
            let transported := localKernelAdditionalActionCompilation closed action outcome
              (by simpa only [localAction, localOutcome] using disjoint)
              (nested.compilation.reindex nested.compilation.reduction.formula
                (by rw [localAction, localOutcome]) rfl)
            exact ⟨transported.reindex transported.reduction.formula
              (by rw [localAction, localOutcome]) rfl, nested.formula_eq⟩
        · let kept := G.ancestralSet remaining (GraphMutilation.none S) outcome
          -- Uncut ancestry marginalizes the actual inherited input.  A
          -- separate rule-3 node removes actions outside that ancestry.
          have outcomeInKept : NodeSet.Subset outcome kept := fun node selected =>
            ancestralSet_contains_targets G remaining (GraphMutilation.none S) outcome
              (outcomeSubset node selected) selected
          let nestedInput := input.marginal kept closed.action_disjoint
            (ancestralSet_subset G remaining (GraphMutilation.none S) outcome)
          let nested := inductionHypothesis nestedInput (closed.ancestral outcome)
            (NodeSet.inter action kept) outcome (NodeSet.inter_subset_right _ _) outcomeInKept
            (NodeSet.Disjoint.of_subset_left disjoint (NodeSet.inter_subset_left _ _)) result
          exact ⟨localKernelPruneCompilation closed action outcome actionSubset outcomeSubset disjoint nested.compilation,
            nested.formula_eq⟩

/-! ## Public joint compilation constructs its initial invariants -/

section PrintedDataAvailability

variable {T : ObservedSignature.{0}} {Γ : ObservedGraph T} {checked : DSeparationCorrectness Γ}

/-- The actual split-branch compiler preserves availability from its computed
children, including interleaved components.  This proof follows the same
family reindexing and final marginal as `localKernelSplitCompilation`; it
does not assume availability of a complete host reduction. -/
noncomputable def localKernelSplitCompilation_printedAvailable
    {remaining externalAction : NodeSet T} (closed : Γ.KernelHostClosed remaining externalAction)
    (action outcome : NodeSet T) (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining) (disjoint : NodeSet.Disjoint action outcome)
    (formulas : NodeSet T → ProbabilityTerm T)
    (nested : forall component, component ∈ Γ.cComponents (NodeSet.diff remaining action) →
      PublishedLocalKernelCompilation Γ checked component (NodeSet.union externalAction (NodeSet.diff remaining component)))
    (aligned : forall component listed, (nested component listed).reduction.formula = formulas component)
    (available : forall component listed, (nested component listed).PrintedAvailable) :
    (localKernelSplitCompilation closed action outcome actionSubset outcomeSubset disjoint formulas nested aligned).compilation.PrintedAvailable := by
  let free := NodeSet.diff remaining action
  let baseAction := NodeSet.union externalAction action
  have discarded : NodeSet.diff remaining free = action := by
    change NodeSet.diff remaining (NodeSet.diff remaining action) = action
    rw [NodeSet.diff_diff, NodeSet.inter_eq_of_subset actionSubset]
  have freeClosed : Γ.KernelHostClosed free baseAction := by
    have restricted := closed.restrict free (NodeSet.diff_subset_left remaining action)
    rw [discarded] at restricted
    exact restricted
  let family : PublishedLocalComponentFamily Γ checked free baseAction := {
    formula := formulas
    compilation := fun component listed => (nested component listed).reindex (formulas component)
      (by
        change ProbabilityTerm.kernel ⟨component,
          NodeSet.union (NodeSet.union externalAction action)
            (NodeSet.diff (NodeSet.diff remaining action) component), NodeSet.empty⟩ = _
        rw [NodeSet.union_assoc, componentAction_from_free_eq remaining action component
          actionSubset (cComponents_subset Γ free listed)])
      (aligned component listed).symm
    formula_eq := fun _component _listed => rfl
  }
  have childAvailable : forall component listed, (family.compilation component listed).PrintedAvailable := by
    intro component listed
    exact (available component listed).reindex (formulas component)
      (by
        change ProbabilityTerm.kernel ⟨component,
          NodeSet.union (NodeSet.union externalAction action)
            (NodeSet.diff (NodeSet.diff remaining action) component), NodeSet.empty⟩ = _
        rw [NodeSet.union_assoc, componentAction_from_free_eq remaining action component
          actionSubset (cComponents_subset Γ free listed)])
      (aligned component listed).symm
  exact (PublishedLocalKernelCompilation.PrintedAvailable.guardedReduction childAvailable freeClosed).marginal
    outcome freeClosed.action_disjoint (outcome_subset_free outcomeSubset disjoint)

/-- Empty-free-host compilation also preserves printed availability.  Its
inherited full-input marginal, source reindexing and empty-outcome rule-3
wrapper add no new printed condition or probability-support assumption. -/
private noncomputable def emptyOutcomeLocalKernelCompilation_printedAvailable
    {remaining externalAction : NodeSet T}
    {input : PublishedLocalKernelCompilation Γ checked remaining externalAction}
    (available : input.PrintedAvailable) (closed : Γ.KernelHostClosed remaining externalAction)
    (action : NodeSet T) (actionSubset : NodeSet.Subset action remaining) :
    (emptyOutcomeLocalKernelCompilation input closed action actionSubset).compilation.PrintedAvailable := by
  let marginal := input.marginal NodeSet.empty closed.action_disjoint
    (fun _node selected => by cases selected)
  have removedEqual : NodeSet.diff remaining NodeSet.empty = remaining := by
    funext node
    exact Bool.and_true (remaining node)
  let nested := marginal.reindex (.marginalize remaining input.reduction.formula) rfl
    (by change ProbabilityTerm.marginalize remaining input.reduction.formula =
          .marginalize (NodeSet.diff remaining NodeSet.empty) input.reduction.formula
        rw [removedEqual])
  have marginalAvailable : marginal.PrintedAvailable := available.marginal NodeSet.empty closed.action_disjoint
    (fun _node selected => by cases selected)
  have nestedAvailable : nested.PrintedAvailable := marginalAvailable.reindex
    (.marginalize remaining input.reduction.formula) rfl
    (by change ProbabilityTerm.marginalize remaining input.reduction.formula =
          .marginalize (NodeSet.diff remaining NodeSet.empty) input.reduction.formula
        rw [removedEqual])
  exact fun model projected reference supported => nestedAvailable model projected reference supported

end PrintedDataAvailability

/-- Every identified public guarded joint query has a formula-aligned
compilation with recursively composed local data.  The observational input
needs only unit data, and full-host parent closure is proved internally. -/
noncomputable def identifyGuardedJointKernelLocalCompilation
    (correct : DSeparationCorrectness G) (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyGuardedJointKernel G query = .identified term) :
    PublishedLocalKernelSuccess G correct query.outcome query.action term := by
  let input := PublishedLocalKernelCompilation.observational G correct
  let compiled := identifyGuardedKernelFuelLocalCompilation (kernelIdentificationFuel S)
    input (ObservedGraph.KernelHostClosed.full G) query.action query.outcome
    (fun _node _selected => rfl) (fun _node _selected => rfl) query.action_outcome_disjoint result
  exact ⟨compiled.compilation.reindex compiled.compilation.reduction.formula
    (by rw [NodeSet.union_empty_left]) rfl, compiled.formula_eq⟩

end Causality
end Thesis
