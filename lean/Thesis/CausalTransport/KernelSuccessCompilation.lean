import Thesis.CausalTransport.KernelProductCompilation
import Thesis.CausalTransport.KernelIdentification

namespace Thesis
namespace Causality

open Probability

/-!
# Structural success compilation for current-kernel ID

The branch constructors certify individual operations of the replacement
algorithm.  This module applies them by induction on the *actual* fuel-bounded
program, rather than enumerating selected combinations of branch names.
Every recursive invocation retains its certified current expression, external
actions, parent closure, and everywhere-positive target invariant.

The output is the engine's literal expression: neither an equivalent hand-
written adjustment formula nor an assumed compiler for the old ID program is
substituted for it.  Product factors are read from their computed outcomes.
A successful collection proves that each listed factor identified; no witness
is selected from a proposition to construct the family of formulas.

This is the success side of completeness, not the final completeness theorem.
Failure-to-hedge transport and a positive countermodel for the original query
are still required to turn semantic identifiability into a successful run.
Neither the soundness implementation nor an assumed completeness package is
imported here.
-/

/-! ## Finite branch alignment without selecting propositional witnesses -/

/-- Read a computed identified formula.  The fallback makes this an ordinary
total syntax function; successful combination proves it is never used on any
listed recursive factor. -/
private def identifiedFormula (outcome : IdentificationOutcome S) : ProbabilityTerm S :=
  match outcome with
  | .identified term => term
  | _ => unitProbabilityTerm S

/-- A successful combination makes every listed invocation identified.
Only a proposition is proved here: the formula itself is obtained by the
preceding explicit pattern match on the computed outcome. -/
private theorem identifiedFormula_eq_of_combined
    {α : Type u} (inputs : List α) (run : α -> IdentificationOutcome S)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
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

/-- The displayed combined term uses exactly the computed factors, in the
collector's original order.  This equality retains repeated inputs and does
not require decidable equality of formulas or of the input index type. -/
private theorem combinedTerm_eq_identifiedFormulas
    {α : Type u} (inputs : List α) (run : α -> IdentificationOutcome S)
    (assemble : List (ProbabilityTerm S) -> ProbabilityTerm S)
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

/-- Local query coordinates already contained in the host are unchanged by
the engine's normalization.  The subset proof is constructive and concerns
only finite Boolean node sets. -/
private theorem intersectHost_eq {selected remaining : NodeSet S}
    (subset : NodeSet.Subset selected remaining) :
    NodeSet.inter selected remaining = selected := by
  rw [NodeSet.inter_comm, NodeSet.inter_eq_of_subset subset]

/-- A disjoint outcome lies in the free host.  This is used both to align
the sole component with its outcome and to retain the original outcome in
a containing-component recursive invocation. -/
private theorem outcome_subset_free {remaining action outcome : NodeSet S}
    (subset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome) :
    NodeSet.Subset outcome (NodeSet.diff remaining action) := by
  intro node selected
  exact Bool.and_eq_true_iff.mpr
    ⟨subset node selected, by rw [disjoint.symm node selected]; rfl⟩

/-- An empty free partition forces a disjoint host outcome to be empty.
Coverage is used only inside `Prop`; the proof never chooses a component to
build a formula or a certificate. -/
private theorem outcome_empty_of_no_components
    (G : ObservedGraph S) (remaining action outcome : NodeSet S)
    (subset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    (partition : G.cComponents (NodeSet.diff remaining action) = []) :
    outcome = NodeSet.empty := by
  funext node
  cases selected : outcome node with
  | false => rfl
  | true =>
      rcases cComponents_covers G (NodeSet.diff remaining action)
        (outcome_subset_free subset disjoint node selected) with ⟨component, listed, _⟩
      rw [partition] at listed
      cases listed

/-! ## The empty-free branch retains the current input marginal -/

/-- Compile the all-host marginal under arbitrary local actions when the
outcome is empty.  Rule 3 deletes those actions with a vacuous path side
condition, then the ordinary marginal compiler reads the certified current
input.  Keeping this branch explicit also covers empty signatures without
assuming that an engine guard is unreachable. -/
private noncomputable def emptyOutcomeCurrentKernelCompilation
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (action : NodeSet S) (actionSubset : NodeSet.Subset action remaining) :
    PublishedPositiveIdentificationCompilation C correct
      (.kernel ⟨NodeSet.empty, NodeSet.union externalAction action, NodeSet.empty⟩)
      (.marginalize remaining input.certificate.formula) := by
  let marginal := currentKernelMarginalPublishedCertificate correct obsPositive
    remaining externalAction NodeSet.empty input.closed.action_disjoint
    (fun _node selected => by cases selected) input.certificate
  have removedEqual : NodeSet.diff remaining NodeSet.empty = remaining := by
    funext node
    exact Bool.and_true (remaining node)
  let nested := marginal.reindex rfl
    (show ProbabilityTerm.marginalize remaining input.certificate.formula = marginal.formula by
      change ProbabilityTerm.marginalize remaining input.certificate.formula =
        .marginalize (NodeSet.diff remaining NodeSet.empty) input.certificate.formula
      rw [removedEqual])
  have four := FourWayDisjoint.of_empty_w externalAction NodeSet.empty action
    (NodeSet.disjoint_empty_right externalAction)
    (NodeSet.disjoint_of_subset_right input.closed.action_disjoint actionSubset)
    (NodeSet.disjoint_empty_left action)
  let deleted := PublishedIdentificationCertificate.prependDoRuleOfPositive obsPositive
    (DoRuleApplication.rule3 (G := G) (separation := pathRuleSeparation G)
      externalAction NodeSet.empty action NodeSet.empty four
      (PathSpecification.PathDSeparated.of_isEmpty_left G _ NodeSet.empty action
        (NodeSet.union externalAction NodeSet.empty) NodeSet.isEmpty_empty)) nested
  exact {
    certificate := deleted.reindex (by rfl) rfl
    formula_eq := rfl
    positive := fun model member reference => ProbabilityTerm.marginalizePositiveSupportedValue
      model remaining input.certificate.formula reference (input.positive model member)
  }

/-! ## Every successful invocation has a formula-aligned positive certificate -/

/-- Compile every successful current-kernel ID invocation by induction on
its fuel.  The finite host may have arbitrary topological gaps and external
actions.  A recursive current input is never replaced by a fresh observational
distribution.

The subset and disjointness hypotheses are query well-formedness invariants,
not unproved graph-separation assumptions.  The product branch obtains its
child success equations from the actual combined result and applies the
induction hypothesis independently to every listed component.  The returned
positivity concerns the engine's exact target syntax at every assignment. -/
noncomputable def identifyKernelFuelPublishedCompilation
    {G : ObservedGraph S} {C : GraphModelClass G} {correct : DSeparationCorrectness G}
    (fuel : Nat) {remaining externalAction : NodeSet S}
    (input : PublishedCurrentKernelInput C correct remaining externalAction)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (action outcome : NodeSet S)
    (actionSubset : NodeSet.Subset action remaining)
    (outcomeSubset : NodeSet.Subset outcome remaining)
    (disjoint : NodeSet.Disjoint action outcome)
    {term : ProbabilityTerm S}
    (result : identifyKernelFuel fuel G remaining outcome action input.certificate.formula =
      .identified term) :
    PublishedPositiveIdentificationCompilation C correct
      (.kernel ⟨outcome, NodeSet.union externalAction action, NodeSet.empty⟩) term := by
  induction fuel generalizing remaining externalAction action outcome term with
  -- Exhaustion cannot supply the identified equation required by the interface.
  | zero => cases result
  | succ fuel inductionHypothesis =>
      have localAction := intersectHost_eq actionSubset
      have localOutcome := intersectHost_eq outcomeSubset
      simp only [identifyKernelFuel, localAction, localOutcome] at result
      split at result
      · rename_i emptyAction
        -- No local intervention: retain the external actions and marginalize
        -- the actual input expression, including its earlier recursive work.
        have actionEmpty := NodeSet.eq_empty_of_isEmpty emptyAction
        cases result
        let marginal := currentKernelMarginalPublishedCertificate correct obsPositive
          remaining externalAction outcome input.closed.action_disjoint outcomeSubset input.certificate
        exact {
          certificate := marginal.reindex (by rw [actionEmpty, NodeSet.union_empty_right]) rfl
          formula_eq := rfl
          positive := fun model member reference => ProbabilityTerm.marginalizePositiveSupportedValue
            model (NodeSet.diff remaining outcome) input.certificate.formula reference
            (input.positive model member)
        }
      · split at result
        · split at result
          · split at result
            · rename_i noComponents
              -- Coverage makes the outcome empty; the explicit empty-query
              -- constructor still certifies the program's full-host marginal.
              have emptyOutcome := outcome_empty_of_no_components G remaining action outcome
                outcomeSubset disjoint noComponents
              cases result
              subst outcome
              exact emptyOutcomeCurrentKernelCompilation input obsPositive action actionSubset
            · rename_i component oneComponent
              have componentEqual := cComponents_eq_of_singleton G
                (NodeSet.diff remaining action) oneComponent
              have outcomeInComponent : NodeSet.Subset outcome component := by
                rw [componentEqual]
                exact outcome_subset_free outcomeSubset disjoint
              split at result
              ·
                -- The single-host-component guard returns failure, not a term.
                cases result
              · split at result
                · rename_i componentListed
                  -- Terminal extraction changes the random host but introduces
                  -- exactly the interventions already present in the query.
                  have listed : component ∈ G.cComponents remaining := by
                    rcases List.any_eq_true.mp componentListed with ⟨piece, included, equal⟩
                    have same := (NodeSet.equal_eq_true_iff piece component).mp equal
                    exact same ▸ included
                  have discardedEqual : NodeSet.diff remaining component = action := by
                    rw [componentEqual, NodeSet.diff_diff, NodeSet.inter_eq_of_subset actionSubset]
                  cases result
                  let componentInput := input.component obsPositive listed
                  let marginal := currentKernelMarginalPublishedCertificate correct obsPositive
                    component (NodeSet.union externalAction (NodeSet.diff remaining component)) outcome
                    componentInput.closed.action_disjoint outcomeInComponent componentInput.certificate
                  exact {
                    certificate := marginal.reindex (by rw [discardedEqual]) rfl
                    formula_eq := rfl
                    positive := fun model member reference => ProbabilityTerm.marginalizePositiveSupportedValue
                      model (NodeSet.diff component outcome) componentInput.certificate.formula reference
                      (componentInput.positive model member)
                  }
                · split at result
                  · rename_i larger containing
                    -- Every outcome stays inside the sole free component and
                    -- therefore inside its containing host.  Discarded host
                    -- vertices were actions already; only their split changes.
                    have specification := containingCComponent_spec G remaining component containing
                    let componentInput := input.component obsPositive specification.1
                    let nested := inductionHypothesis componentInput
                      (NodeSet.inter action larger) outcome (NodeSet.inter_subset_right _ _)
                      (outcomeInComponent.trans specification.2)
                      (NodeSet.Disjoint.of_subset_left disjoint (NodeSet.inter_subset_left _ _)) result
                    have discarded : NodeSet.Subset (NodeSet.diff remaining larger) action := by
                      have obtained := currentKernelRestrictionDiscardedAction_of_containing G
                        remaining action (by simpa only [localAction] using oneComponent) containing
                      simpa only [localAction] using obtained
                    exact {
                      certificate := currentKernelRestrictionPublishedCertificate remaining larger
                        externalAction action outcome actionSubset discarded nested.certificate
                      formula_eq := nested.formula_eq
                      positive := nested.positive
                    }
                  · cases result
            · let run := fun component => identifyKernelFuel fuel G remaining component
                (NodeSet.diff remaining component) input.certificate.formula
              -- Read the real child outputs first.  Successful combination
              -- proves every listed child equation, so induction constructs
              -- the certificate family without choosing existential witnesses.
              let formulas := fun component => identifiedFormula (run component)
              let nested := fun component (listed : component ∈ G.cComponents (NodeSet.diff remaining action)) =>
                inductionHypothesis input (NodeSet.diff remaining component) component
                  (NodeSet.diff_subset_left _ _)
                  ((cComponents_subset G _ listed).trans (NodeSet.diff_subset_left _ _))
                  (NodeSet.disjoint_diff_right _ _)
                  (identifiedFormula_eq_of_combined _ run _ result listed)
              let compiled := currentKernelSplitCompilation input obsPositive action outcome
                actionSubset outcomeSubset disjoint formulas
                (fun component listed => (nested component listed).certificate)
                (fun component listed => (nested component listed).formula_eq)
                (fun component listed => (nested component listed).positive)
              have termAlignment := combinedTerm_eq_identifiedFormulas _ run _ result
              exact {
                certificate := compiled.certificate
                formula_eq := compiled.formula_eq.trans termAlignment.symm
                positive := fun model member reference => by
                  rw [termAlignment]
                  exact compiled.positive model member reference
              }
          · let additional := identificationAdditionalAction G remaining outcome action
            -- Augmentation changes only the query action.  The current input
            -- and its positive-support invariant are passed through unchanged.
            have additionalSubset := identificationAdditionalAction_subset_remaining G remaining outcome action
            have additionalDisjoint := identificationAdditionalAction_disjoint_outcome G remaining outcome action
            have additionalOutcome : NodeSet.Disjoint additional outcome := by
              simpa only [localOutcome] using additionalDisjoint
            let nested := inductionHypothesis input (NodeSet.union action additional) outcome
              (NodeSet.union_subset actionSubset additionalSubset)
              outcomeSubset (NodeSet.disjoint_union_left_of disjoint additionalOutcome) result
            let transported := currentKernelAdditionalActionPublishedCertificate input obsPositive action outcome
              (by simpa only [localAction, localOutcome] using disjoint)
              (nested.certificate.reindex (by rw [localAction, localOutcome]) rfl)
            exact {
              certificate := transported.reindex (by rw [localAction, localOutcome]) rfl
              formula_eq := nested.formula_eq
              positive := nested.positive
            }
        · let kept := G.ancestralSet remaining (GraphMutilation.none S) outcome
          -- Ordinary ancestry preserves the outcome and marginalizes the
          -- current input.  The separate rule-3 transport removes the actions
          -- outside that ancestry from the query, not from the input formula.
          have outcomeInKept : NodeSet.Subset outcome kept := fun node selected =>
            ancestralSet_contains_targets G remaining (GraphMutilation.none S) outcome
              (outcomeSubset node selected) selected
          let nestedInput := input.ancestral obsPositive outcome
          let nested := inductionHypothesis nestedInput (NodeSet.inter action kept) outcome
            (NodeSet.inter_subset_right _ _) outcomeInKept
            (NodeSet.Disjoint.of_subset_left disjoint (NodeSet.inter_subset_left _ _)) result
          exact {
            certificate := currentKernelPrunePublishedCertificate input obsPositive action outcome
              actionSubset outcomeSubset disjoint nested.certificate
            formula_eq := nested.formula_eq
            positive := nested.positive
          }

/-! ## Public joint success needs no caller-supplied current-input invariant -/

/-- The replacement joint engine's every identified result has a supported,
action-free published derivation and an everywhere-positive target.  The
initial current input is the full observational joint, so all recursive
input invariants are constructed internally.  This theorem is independent
of any semantic identifiability assumption or general hedge countermodel. -/
noncomputable def identifyJointKernelPublishedCompilation
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyJointKernel G query = .identified term) :
    PublishedPositiveIdentificationCompilation C correct query.sourceTerm term := by
  let input := PublishedCurrentKernelInput.observational correct obsPositive
  let compiled := identifyKernelFuelPublishedCompilation (kernelIdentificationFuel S)
    input obsPositive query.action query.outcome
    (fun _node _selected => rfl) (fun _node _selected => rfl)
    query.action_outcome_disjoint result
  exact {
    certificate := compiled.certificate.reindex (by rw [NodeSet.union_empty_left]; rfl) rfl
    formula_eq := compiled.formula_eq
    positive := compiled.positive
  }

/-- Expose public success compilation in the query-indexed published
certificate interface.  Reindexing makes the engine output definitionally
visible as the certificate formula; no equality of numerical denotations is
used to establish this syntactic alignment. -/
noncomputable def identifyJointKernelPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyJointKernel G query = .identified term) :
    PublishedJointCertificate C correct query where
  toPublishedIdentificationCertificate :=
    let compiled := identifyJointKernelPublishedCompilation correct obsPositive query result
    compiled.certificate.reindex rfl compiled.formula_eq.symm

/-- The query-indexed wrapper returns precisely the successful engine term,
including all nested marginals and prefix denominators. -/
theorem identifyJointKernelPublishedCertificate_formula
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyJointKernel G query = .identified term) :
    (identifyJointKernelPublishedCertificate correct obsPositive query result).formula = term := rfl

end Causality
end Thesis
