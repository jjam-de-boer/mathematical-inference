import Thesis.Examples.ConditionalPromotionSupport
import Thesis.Causality.ProbabilityTermEquality

namespace Thesis
namespace Causality
namespace Examples
namespace NullActionPromotionCompilation

open Probability GuardedKernelZeroRegression

/-!
# Recursive local data for the null-action promotion regression

The guarded joint call after mediator promotion prunes `Z`, extracts the
containing component `{X,Y}` under `do(M)`, then prunes `X` before the empty-
action marginal.  This fixture supplies primitive data for those actual
constructors rather than assuming a whole support tree or observational
positivity.  The inherited observational data is unit at every finite variant.

The `X` factor is supported at both labels.  Its denominator is positive,
but its weight is zero at `X = true`.  For `Y`, either positive prefix guard
forces `X = false`; only there are predecessor overlap and the displayed
denominator requested.  Thus a genuinely undefined quotient is skipped, not
assigned a value.  Finite checks range over the complete supplied assignment
enumeration, not just the final reference cell.
-/

private abbrev nativeModel := NullActionPromotionSupport.model
private abbrev graph := projection.observedGraph
private abbrev correct := graph.dSeparationCorrectness

def host : NodeSet signature := graph.ancestralSet NodeSet.full (.none signature) (NodeSet.singleton y)
def component : NodeSet signature := NodeSet.union (NodeSet.singleton x) (NodeSet.singleton y)

private theorem host_subset : NodeSet.Subset host NodeSet.full :=
  ancestralSet_subset graph NodeSet.full (.none signature) (NodeSet.singleton y)

private theorem host_closed : graph.KernelHostClosed host NodeSet.empty :=
  (ObservedGraph.KernelHostClosed.full graph).ancestral (NodeSet.singleton y)

private theorem component_listed : component ∈ graph.cComponents host := by decide +kernel

/-- Ancestral restriction keeps the actual initial expression and requests
only its unit data at the `Z` variants used by this marginal. -/
noncomputable def ancestralInput :=
  (PublishedLocalKernelCompilation.observational graph correct).marginal host
    (NodeSet.disjoint_empty_left _) host_subset

noncomputable def componentInput := ancestralInput.ofComponent host_closed component_listed

/-- Pure syntax is named separately from its proof-carrying record.  Finite
checks can inspect it without unfolding the support constructor. -/
private def ancestralFormula : ProbabilityTerm signature :=
  .marginalize (NodeSet.diff NodeSet.full host) (observationalJointTerm signature)

/-! ## Reflect finite primitive checks into constructive value data -/

private theorem checkedAt (test : signature.Assignment → Bool)
    (checked : signature.assignmentEnumeration.all test = true) (reference : signature.Assignment) :
    test reference = true :=
  (List.all_eq_true.mp checked) reference (signature.assignmentEnumeration_complete reference)

/-- Read the value already present in a positive result.  There is no
proposition-to-witness selection or completion of an undefined result. -/
private noncomputable def positiveValueOfTest (result : ProbabilityResult.Result)
    (positive : result.any (fun value => decide (0 < value.num)) = true) :
    ProbabilityResult.PositiveSupportedValue result := by
  cases result with
  | none => cases positive
  | some value => exact ⟨value, .value (QProb.equiv_refl _), of_decide_eq_true positive⟩

private noncomputable def collapsedPositive (term : ProbabilityTerm signature) (reference : signature.Assignment)
    (positive : (nativeModel.termDenote term reference).any (fun value => decide (0 < value.num)) = true) :
    ProbabilityResult.PositiveSupportedValue (term.denote nativeModel.toLatentRootSCM reference) := by
  rw [← nativeModel.termDenote_preserved term reference]
  exact positiveValueOfTest _ positive

private theorem positive_impossible_of_zero {result : ProbabilityResult.Result}
    (zero : result.map (fun value => value.num) = some 0)
    (positive : ProbabilityResult.PositiveSupportedValue result) : False := by
  cases result with
  | none => cases positive.equivalent
  | some value =>
      have numeratorZero : value.num = 0 := Option.some.inj zero
      cases positive.equivalent with
      | value equivalent =>
          have actualPositive := (QProb.equiv_num_pos_iff equivalent).mpr positive.positive
          rw [numeratorZero] at actualPositive
          exact Nat.not_lt_zero _ actualPositive

/-! ## Local factor inputs, at precisely their demanded references -/

private def denominatorTerm (node : Fin signature.count) : ProbabilityTerm signature :=
  .marginalize (NodeSet.diff host (chainCondition host node)) ancestralFormula

/-- The empty cylinder has positive mass by the record's normalization,
even when many observed cells are zero.  No model-class positivity is used. -/
private noncomputable def emptyPositive (reference : signature.Assignment) :
    ProbabilityResult.PositiveSupportedValue
      ((ProbabilityTerm.kernel ⟨NodeSet.empty, NodeSet.empty, NodeSet.empty⟩).denote
        nativeModel.toLatentRootSCM reference) := by
  let distribution := (Kernel.mk NodeSet.empty NodeSet.empty NodeSet.empty).distribution
    nativeModel.toLatentRootSCM reference
  let value := distribution.probVal (Kernel.agreesOn NodeSet.empty reference)
  have normalized : QProb.Equiv value QProb.one := QProb.equiv_trans
    (distribution.probVal_congr _ Probability.topEvent (fun _sample => by
      simp [Kernel.agreesOn, NodeSet.empty, Probability.topEvent, finAll_true])) distribution.normalization
  exact ⟨value, Kernel.unconditionalDenote nativeModel.toLatentRootSCM NodeSet.empty NodeSet.empty reference,
    (QProb.equiv_num_pos_iff normalized).mpr (by decide)⟩

/-- Intrinsic finite marginalization and full observational marginal
normalization prove the displayed first denominator positive.  This avoids
an expensive repeated numerical check, and does not invoke graph-indexed
derivation soundness or assume the component's yet-to-be-built support. -/
private noncomputable def xDenominatorPositive (reference : signature.Assignment) :
    ProbabilityResult.PositiveSupportedValue ((denominatorTerm x).denote nativeModel.toLatentRootSCM reference) := by
  have syntax : denominatorTerm x = .marginalize host ancestralFormula :=
    (ProbabilityTerm.equal_eq_true_iff _ _).mp (by decide +kernel)
  rw [syntax]
  have marginal : ProbabilityTerm.EquivalentAt nativeModel.toLatentRootSCM
      (.kernel ⟨NodeSet.empty, NodeSet.empty, NodeSet.empty⟩)
      (.marginalize host (.kernel ⟨host, NodeSet.empty, NodeSet.empty⟩)) reference := by
    simpa only [NodeSet.union_empty_left] using
      (ProbabilityTerm.marginalization_equivalentAt nativeModel.toLatentRootSCM NodeSet.empty NodeSet.empty host
        NodeSet.empty reference
        (FourWayDisjoint.of_empty_w _ _ _ (NodeSet.disjoint_empty_left _) (NodeSet.disjoint_empty_left _)
          (NodeSet.disjoint_empty_left _))
        (Kernel.unconditional_supportedAt nativeModel.toLatentRootSCM NodeSet.empty NodeSet.empty reference))
  have input := ProbabilityTerm.marginalize_congrAt nativeModel.toLatentRootSCM host reference
    (fun variant _listed => ProbabilityTerm.emptyActionKernel_equiv_fullMarginal nativeModel.toLatentRootSCM host variant)
  exact ProbabilityResult.PositiveSupportedValue.transport (ProbabilityResult.trans marginal input) (emptyPositive reference)

private noncomputable def xInputs (reference : signature.Assignment) :
    LocalComponentFactorData ancestralInput nativeModel.toLatentRootSCM reference x where
  overlap := by
    change 0 < (nativeModel.toLatentRootSCM.observationalDist.probVal
      (Kernel.agreesOn (NodeSet.union NodeSet.empty (chainCondition host x)) reference)).num
    rw [nativeModel.toLatentRootSCM_observationalDist]
    exact of_decide_eq_true (checkedAt (fun assignment => decide
      (0 < (nativeModel.observationalDist.probVal
        (Kernel.agreesOn (NodeSet.union NodeSet.empty (chainCondition host x)) assignment)).num))
      (by decide +kernel) reference)
  numeratorData := fun _variant _listed _originalVariant _originalListed => ()
  denominatorData := fun _variant _listed _originalVariant _originalListed => ()
  denominatorPositive := xDenominatorPositive reference

private noncomputable def yInputs (reference : signature.Assignment) (supportedX : reference x = false) :
    LocalComponentFactorData ancestralInput nativeModel.toLatentRootSCM reference y where
  overlap := by
    change 0 < (nativeModel.toLatentRootSCM.observationalDist.probVal
      (Kernel.agreesOn (NodeSet.union NodeSet.empty (chainCondition host y)) reference)).num
    rw [nativeModel.toLatentRootSCM_observationalDist]
    have checked : signature.assignmentEnumeration.all (fun assignment => decide
        (assignment x = false → 0 < (nativeModel.observationalDist.probVal
          (Kernel.agreesOn (NodeSet.union NodeSet.empty (chainCondition host y)) assignment)).num)) = true := by
      decide +kernel
    exact (of_decide_eq_true (checkedAt _ checked reference)) supportedX
  numeratorData := fun _variant _listed _originalVariant _originalListed => ()
  denominatorData := fun _variant _listed _originalVariant _originalListed => ()
  denominatorPositive := collapsedPositive (denominatorTerm y) reference (by
    have checked : signature.assignmentEnumeration.all (fun assignment => decide
        (assignment x = false → (nativeModel.termDenote (denominatorTerm y) assignment).any
          (fun value => decide (0 < value.num)) = true)) = true := by decide +kernel
    exact (of_decide_eq_true (checkedAt _ checked reference)) supportedX)

private def sourceYPrefix : ProbabilityTerm signature :=
  .kernel ⟨chainPrefix component y.val, componentExternalAction host NodeSet.empty component, NodeSet.empty⟩

private def displayedYPrefix : ProbabilityTerm signature :=
  guardedComponentPrefixTerm host ancestralFormula component y.val (Nat.le_of_lt y.isLt)

/-- Each guard is checked separately.  Source support is not inferred from
the displayed prefix, nor displayed positivity from denotational soundness. -/
private theorem x_false_of_y_guard (reference : signature.Assignment)
    (branch : Sum
      (ProbabilityResult.PositiveSupportedValue (sourceYPrefix.denote nativeModel.toLatentRootSCM reference))
      (ProbabilityResult.PositiveSupportedValue (displayedYPrefix.denote nativeModel.toLatentRootSCM reference))) :
    reference x = false := by
  cases selected : reference x with
  | false => rfl
  | true =>
      have sourceZero : (sourceYPrefix.denote nativeModel.toLatentRootSCM reference).map (fun value => value.num) = some 0 := by
        rw [← nativeModel.termDenote_preserved sourceYPrefix reference]
        have checked : signature.assignmentEnumeration.all (fun assignment => decide
            (assignment x = true → (nativeModel.termDenote sourceYPrefix assignment).map
              (fun value => value.num) = some 0)) = true := by decide +kernel
        exact (of_decide_eq_true (checkedAt _ checked reference)) selected
      have displayedZero : (displayedYPrefix.denote nativeModel.toLatentRootSCM reference).map (fun value => value.num) = some 0 := by
        rw [← nativeModel.termDenote_preserved displayedYPrefix reference]
        have checked : signature.assignmentEnumeration.all (fun assignment => decide
            (assignment x = true → (nativeModel.termDenote displayedYPrefix assignment).map
              (fun value => value.num) = some 0)) = true := by decide +kernel
        exact (of_decide_eq_true (checkedAt _ checked reference)) selected
      cases branch with
      | inl positive => exact False.elim (positive_impossible_of_zero sourceZero positive)
      | inr positive => exact False.elim (positive_impossible_of_zero displayedZero positive)

/-- Primitive data for the entire extracted component at every reference.
The two inherited finite families are built from unit observational data;
null prefix branches require no `Y` quotient data at all. -/
noncomputable def componentData (reference : signature.Assignment) :
    componentInput.Data nativeModel.toLatentRootSCM reference := by
  change LocalComponentData ancestralInput component nativeModel.toLatentRootSCM reference
  intro node selected branch
  if atX : node = x then
    subst node
    exact xInputs reference
  else
    have same : node = y := by
      change (NodeSet.singleton x node || NodeSet.singleton y node) = true at selected
      rcases Bool.or_eq_true_iff.mp selected with first | second
      · exact False.elim (atX (of_decide_eq_true first))
      · exact of_decide_eq_true second
    subst node
    exact yInputs reference (x_false_of_y_guard reference branch)

/-- The ordinary native tree is an output of the local-data constructor,
not a field supplied in the fixture's primitive data. -/
noncomputable def component_supported (reference : signature.Assignment) :
    HiddenDAGLocalDerivationSupport nativeModel reference
      (componentInput.reduction.derivation.compile correct) :=
  componentInput.hiddenDAG_supportedAt nativeModel reference (componentData reference)

/-! ## Reassemble the exact recursive joint and conditional expression -/

private def componentAction : NodeSet signature := componentExternalAction host NodeSet.empty component

private theorem component_closed : graph.KernelHostClosed component componentAction :=
  host_closed.restrict component (cComponents_subset graph host component_listed)

private theorem y_subset_component : NodeSet.Subset (NodeSet.singleton y) component :=
  NodeSet.subset_union_right _ _

/-- Ancestry inside `{X,Y}` drops `X`.  The final empty-action invocation
still prints its empty complementary marginal; neither marginal is erased. -/
private noncomputable def firstMarginal :=
  componentInput.marginal (NodeSet.singleton y) component_closed.action_disjoint y_subset_component

private noncomputable def finalMarginal :=
  firstMarginal.marginal (NodeSet.singleton y)
    (NodeSet.disjoint_of_subset_right component_closed.action_disjoint y_subset_component)
    (fun _node selected => selected)

private noncomputable def innerPruneInput :
    PublishedLocalKernelCompilation graph correct (NodeSet.singleton y)
      (NodeSet.union componentAction (NodeSet.inter (NodeSet.singleton x)
        (graph.ancestralSet component (.none signature) (NodeSet.singleton y)))) :=
  finalMarginal.reindex finalMarginal.reduction.formula (by decide +kernel) rfl

private noncomputable def innerPruned :=
  localKernelPruneCompilation component_closed (NodeSet.singleton x) (NodeSet.singleton y)
    (NodeSet.subset_union_left _ _) y_subset_component
    (NodeSet.disjoint_singletons_of_ne (by decide)) innerPruneInput

private def action : NodeSet signature := NodeSet.union (NodeSet.singleton x) (NodeSet.singleton mediator)

private noncomputable def outerPruneInput :
    PublishedLocalKernelCompilation graph correct (NodeSet.singleton y)
      (NodeSet.union NodeSet.empty (NodeSet.inter action host)) :=
  innerPruned.reindex innerPruned.reduction.formula (by decide +kernel) rfl

private noncomputable def outerPruned :=
  localKernelPruneCompilation (ObservedGraph.KernelHostClosed.full graph) action (NodeSet.singleton y)
    (fun _node _selected => rfl) (fun _node _selected => rfl)
    (NodeSet.disjoint_union_left_of (NodeSet.disjoint_singletons_of_ne (by decide))
      (NodeSet.disjoint_singletons_of_ne (by decide))) outerPruneInput

private def promotedQuery :=
  NullActionPromotionSupport.query.exchangeCondition NullActionPromotionSupport.step.node
    NullActionPromotionSupport.step.selected

/-- Source equalities retain the original query's external/local action
split.  They change no expression or support data and add no semantic law. -/
noncomputable def jointCompilation :
    PublishedLocalKernelCompilation graph correct promotedQuery.jointNumerator.outcome promotedQuery.action :=
  outerPruned.reindex outerPruned.reduction.formula (by decide +kernel) rfl

/-- Readable pure syntax for the actual retained nested marginals.  This is
used for finite checks and literal alignment, not as a replacement formula. -/
def jointFormula : ProbabilityTerm signature :=
  .marginalize (NodeSet.diff (NodeSet.singleton y) (NodeSet.singleton y))
    (.marginalize (NodeSet.diff component (NodeSet.singleton y))
      (guardedComponentTerm host ancestralFormula component))

theorem jointCompilation_formula : jointCompilation.reduction.formula = jointFormula := rfl

/-- Every marginal variant receives the actual component's local data,
including the variant with a zero `X` prefix.  No complete tree is supplied. -/
noncomputable def jointData (reference : signature.Assignment) :
    jointCompilation.Data nativeModel.toLatentRootSCM reference :=
  fun _finalVariant _finalListed componentVariant _componentListed => componentData componentVariant

private noncomputable def bayesCompilation := localConditionalBayesCompilation promotedQuery jointCompilation

private def bayesDenominator : ProbabilityTerm signature :=
  .marginalize (NodeSet.diff promotedQuery.jointNumerator.outcome promotedQuery.condition) jointFormula

private noncomputable def bayesData (reference : signature.Assignment) :
    bayesCompilation.Data nativeModel.toLatentRootSCM reference := by
  refine {
    sourceSupported := ?_
    numeratorData := jointData reference
    denominatorData := fun variant _listed => jointData variant
    denominatorPositive := ?_
  }
  · have empty : promotedQuery.condition = NodeSet.empty := by decide +kernel
    apply nativeModel.termSupportedAt_to_collapsed promotedQuery.sourceTerm reference
    change nativeModel.TermSupportedAt
      (.kernel ⟨promotedQuery.outcome, promotedQuery.action, promotedQuery.condition⟩) reference
    rw [empty]
    exact nativeModel.kernelSupportedAt_unconditional _ _ reference
  · exact collapsedPositive bayesDenominator reference
      (checkedAt (fun assignment => (nativeModel.termDenote bayesDenominator assignment).any
        (fun value => decide (0 < value.num))) (by decide +kernel) reference)

/-- The promotion and terminal Bayes constructors compose the complete
conditional tree, preserving both intermediate support endpoints. -/
noncomputable def conditionalCompilation :=
  localConditionalExchangeCompilation NullActionPromotionSupport.query NullActionPromotionSupport.step bayesCompilation

noncomputable def conditionalData : conditionalCompilation.Data nativeModel.toLatentRootSCM reference where
  sourceSupported := nativeModel.termSupportedAt_to_collapsed _ _ NullActionPromotionSupport.original_supported
  nestedData := bayesData reference

/-- Compare literal finite syntax against the computed program expression.
No numerical equivalence, cancellation or product regrouping substitutes
for this exact formula alignment. -/
theorem exact_program_formula : conditionalCompilation.formula = NullActionPromotionSupport.formula := by
  apply (ProbabilityTerm.equal_eq_true_iff _ _).mp
  decide +kernel

/-- The full native support tree is constructed from the primitive data at
every demanded recursive reference, not merely checked at its endpoints. -/
noncomputable def native_supported :
    HiddenDAGLocalDerivationSupport nativeModel reference (conditionalCompilation.derivation.compile correct) :=
  conditionalCompilation.hiddenDAG_supportedAt nativeModel reference conditionalData

/-- Interpret the exact engine expression using the assembled ordinary
derivation and native soundness, rather than a bespoke numerical identity. -/
noncomputable def native_sound : nativeModel.TermEquivalentAt NullActionPromotionSupport.query.sourceTerm
    NullActionPromotionSupport.formula reference := by
  have sound := conditionalCompilation.hiddenDAG_soundAt nativeModel reference conditionalData
  rw [exact_program_formula] at sound
  exact sound

end NullActionPromotionCompilation
end Examples
end Causality
end Thesis
