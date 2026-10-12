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
  .marginalize (NodeSet.diff host (chainCondition host node)) ancestralInput.reduction.formula

private noncomputable def xInputs (reference : signature.Assignment) :
    LocalComponentFactorData ancestralInput nativeModel.toLatentRootSCM reference x where
  overlap := by
    change 0 < (nativeModel.toLatentRootSCM.observationalDist.probVal
      (Kernel.agreesOn (NodeSet.union NodeSet.empty (chainCondition host x)) reference)).num
    rw [nativeModel.toLatentRootSCM_observationalDist]
    exact of_decide_eq_true (checkedAt _ (by decide +kernel) reference)
  numeratorData := fun _variant _listed _originalVariant _originalListed => ()
  denominatorData := fun _variant _listed _originalVariant _originalListed => ()
  denominatorPositive := collapsedPositive (denominatorTerm x) reference
    (checkedAt _ (by decide +kernel) reference)

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
  guardedComponentPrefixTerm host ancestralInput.reduction.formula component y.val (Nat.le_of_lt y.isLt)

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
  rcases (NodeSet.union_eq_true (NodeSet.singleton x) (NodeSet.singleton y) node).mp selected with atX | atY
  · have same : node = x := of_decide_eq_true atX
    subst node
    exact xInputs reference
  · have same : node = y := of_decide_eq_true atY
    subst node
    exact yInputs reference (x_false_of_y_guard reference branch)

/-- The ordinary native tree is an output of the local-data constructor,
not a field supplied in the fixture's primitive data. -/
noncomputable def component_supported (reference : signature.Assignment) :
    HiddenDAGLocalDerivationSupport nativeModel reference
      (componentInput.reduction.derivation.compile correct) :=
  componentInput.hiddenDAG_supportedAt nativeModel reference (componentData reference)

end NullActionPromotionCompilation
end Examples
end Causality
end Thesis
