import Thesis.CausalTransport.HiddenDAGComponentFamilyCompilation
import Thesis.Examples.HiddenDAGKernelCompilation

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGComponentFamilyCompilation

open Probability HiddenDAGCollapse

/-!
# Native component-family assembly with a noncanonical root and zeros

Reuse the original five-node hidden relay.  Its observed `Y = true` event is
null, and one collapsed root has three observed children.  The projected
graph's full host is one c-component; its independent current input is the
actual observational joint reduction, not a positive-model certificate.

The native `X` quotient has a unit denominator.  The next `Y` quotient has
the positive `X = true` denominator but a zero numerator.  Both host-prefix
guards are therefore zero before `Z`, whose exact quotient is undefined.
Only the first two factors receive native input subtrees and denominator
data.  The general adapter constructs the complete native host tree, which
the existing native soundness theorem interprets in this original DAG.
-/

/-- Supply this concrete finite comparison explicitly instead of inheriting
an unrelated probability-module instance. A declaration, rather than a local
let, also keeps the kernel-generated decision lemma closed over constants. -/
private instance componentDecidableEq : DecidableEq (NodeSet signature) :=
  FiniteProduct.assignmentDecidableEq signature.count (fun _ => Bool) (fun _ => inferInstance)

private theorem partition_eq : projection.observedGraph.cComponents NodeSet.full = [NodeSet.full] := by
  decide +kernel

/-- The computed lookup is the full component extensionally.  It need not
reduce to the literal full-set function definitionally, so denominator
alignment below uses this actual partition theorem rather than guessing. -/
private theorem componentAt_full (node : Fin signature.count) :
    projection.observedGraph.componentAt NodeSet.full node = NodeSet.full := by
  have listed := (projection.observedGraph.componentAt_spec NodeSet.full node rfl).1
  rw [partition_eq] at listed
  exact List.mem_singleton.mp listed

/-- Reindex the independently available input only at actual listed
components.  The formula remains the original current expression; the
source equality is geometry, not an assumed probability identity. -/
private def componentInput (component : NodeSet signature)
    (listed : component ∈ projection.observedGraph.cComponents NodeSet.full) :
    PublishedCurrentKernelReduction projection.observedGraph component
      (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full component)) where
  formula := HiddenDAGKernelCompilation.input.formula
  actionFree := HiddenDAGKernelCompilation.input.actionFree
  derivation := DoCalculusDerivation.eqCongr (G := projection.observedGraph)
    (separation := pathRuleSeparation projection.observedGraph)
    (by
      have same : component = NodeSet.full := by
        rw [partition_eq] at listed
        exact List.mem_singleton.mp listed
      rw [same]
      rfl)
    rfl HiddenDAGKernelCompilation.input.derivation

noncomputable def family : PublishedComponentKernelReductionFamily projection.observedGraph NodeSet.full NodeSet.empty := {
  formula := fun _component => HiddenDAGKernelCompilation.input.formula
  reduction := componentInput
  formula_eq := fun _component _listed => rfl
}

/-- All actual component marginal variants have native input trees, including
zero observed cells.  The source is an unconditional native cylinder and
the inner observational tree comes from the general initializer. -/
private noncomputable def componentInput_supported (component : NodeSet signature)
    (listed : component ∈ projection.observedGraph.cComponents NodeSet.full) (variant : signature.Assignment) :
    HiddenDAGLocalDerivationSupport model variant
      ((componentInput component listed).derivation.compile projection.observedGraph.dSeparationCorrectness) := by
  let source := model.kernelSupportedAt_unconditional component
    (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full component)) variant
  let inner := HiddenDAGKernelCompilation.input_supported variant
  dsimp [componentInput, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  exact ⟨source, ⟨inner.2.1, inner⟩⟩

private noncomputable def firstInputs :
    HiddenDAGComponentFamilyFactorInputs family model HiddenDAGSoundness.reference x (by rfl) where
  componentSupported := model.kernelSupportedAt_of_observational_overlap _ HiddenDAGSoundness.reference (by
    unfold FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt
    decide +kernel)
  overlap := by unfold FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt; decide +kernel
  numeratorInputSupport := fun variant _listed => componentInput_supported
    (projection.observedGraph.componentAt NodeSet.full x)
    (projection.observedGraph.componentAt_spec NodeSet.full x rfl).1 variant
  denominatorInputSupport := fun variant _listed => componentInput_supported
    (projection.observedGraph.componentAt NodeSet.full x)
    (projection.observedGraph.componentAt_spec NodeSet.full x rfl).1 variant
  denominatorPositive := by
    rw [family.formula_eq]
    change ProbabilityResult.PositiveSupportedValue (model.termDenote
      (.marginalize
        (NodeSet.diff (projection.observedGraph.componentAt NodeSet.full x)
          (chainCondition (projection.observedGraph.componentAt NodeSet.full x) x))
        HiddenDAGKernelCompilation.input.formula) HiddenDAGSoundness.reference)
    rw [componentAt_full x]
    refine ⟨QProb.one, .value ?_, ?_⟩ <;> decide +kernel

private noncomputable def secondInputs :
    HiddenDAGComponentFamilyFactorInputs family model HiddenDAGSoundness.reference y (by rfl) where
  componentSupported := model.kernelSupportedAt_of_observational_overlap _ HiddenDAGSoundness.reference (by
    unfold FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt
    decide +kernel)
  overlap := by unfold FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt; decide +kernel
  numeratorInputSupport := fun variant _listed => componentInput_supported
    (projection.observedGraph.componentAt NodeSet.full y)
    (projection.observedGraph.componentAt_spec NodeSet.full y rfl).1 variant
  denominatorInputSupport := fun variant _listed => componentInput_supported
    (projection.observedGraph.componentAt NodeSet.full y)
    (projection.observedGraph.componentAt_spec NodeSet.full y rfl).1 variant
  denominatorPositive := by
    rw [family.formula_eq]
    change ProbabilityResult.PositiveSupportedValue (model.termDenote
      (.marginalize
        (NodeSet.diff (projection.observedGraph.componentAt NodeSet.full y)
          (chainCondition (projection.observedGraph.componentAt NodeSet.full y) y))
        HiddenDAGKernelCompilation.input.formula) HiddenDAGSoundness.reference)
    rw [componentAt_full y]
    exact HiddenDAGKernelCompilation.denominator_positive

private theorem positive_impossible_of_zero {result : ProbabilityResult.Result}
    (zero : result.map (fun value => value.num) = some 0)
    (positive : ProbabilityResult.PositiveSupportedValue result) : False := by
  cases result with
  | none => cases positive.equivalent
  | some value =>
      have numeratorZero : value.num = 0 := Option.some.inj zero
      cases positive.equivalent with
      | value same =>
          have numeratorPositive := (QProb.equiv_num_pos_iff same).mpr positive.positive
          rw [numeratorZero] at numeratorPositive
          exact Nat.not_lt_zero _ numeratorPositive

/-- Finite index decisions construct only the two needed data records.
At the last vertex, explicit native zero values refute each positive guard;
no `Z` conditional, input tree or positive denominator is asserted. -/
private noncomputable def conditions :
    HiddenDAGComponentFamilySupportConditions family model HiddenDAGSoundness.reference := by
  intro node _selected branch
  if atFirst : node.val = 0 then
    have same : node = x := Fin.ext atFirst
    subst node
    exact firstInputs
  else if atSecond : node.val = 1 then
    have same : node = y := Fin.ext atSecond
    subst node
    exact secondInputs
  else
    have bound : node.val < 3 := node.isLt
    have atThird : node.val = 2 := by omega
    have same : node = z := Fin.ext atThird
    subst node
    cases branch with
    | inl sourcePositive =>
        have zero : (model.termDenote (.kernel ⟨chainPrefix NodeSet.full z.val, NodeSet.empty, NodeSet.empty⟩)
            HiddenDAGSoundness.reference).map (fun value => value.num) = some 0 := by
          decide +kernel
        exact False.elim (positive_impossible_of_zero zero sourcePositive)
    | inr targetPositive =>
        have zero : (model.termDenote
            (GuardedHostChain.prefixTerm NodeSet.full family.factor z.val (Nat.le_of_lt z.isLt))
            HiddenDAGSoundness.reference).map (fun value => value.num) = some 0 := by
          decide +kernel
        exact False.elim (positive_impossible_of_zero zero targetPositive)

noncomputable def reduction := family.guardedReduction (ObservedGraph.KernelHostClosed.full projection.observedGraph)

noncomputable def supported : HiddenDAGLocalDerivationSupport model HiddenDAGSoundness.reference
    (reduction.derivation.compile projection.observedGraph.dSeparationCorrectness) :=
  family.hiddenDAG_guardedReduction_supportedAt (ObservedGraph.KernelHostClosed.full projection.observedGraph)
    model HiddenDAGSoundness.reference conditions

noncomputable def sound : model.TermEquivalentAt
    (.kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩) reduction.formula HiddenDAGSoundness.reference :=
  (reduction.derivation.compile projection.observedGraph.dSeparationCorrectness).hiddenDAG_denotational_soundAt supported

theorem guarded_host_is_supported_zero :
    (model.termDenote reduction.formula HiddenDAGSoundness.reference).map (fun value => value.num) = some 0 := by
  decide +kernel

theorem skipped_last_quotient_is_undefined :
    (model.termDenote (family.factor z) HiddenDAGSoundness.reference).isNone = true := by
  decide +kernel

theorem model_is_not_positive : ¬ model.ObservationallyPositive := HiddenDAGIdentification.zero_model_not_positive

theorem collapsed_model_is_not_canonical : ¬ model.toLatentRootSCM.IsCanonicalSemiMarkovian :=
  HiddenDAGCollapse.collapsed_not_canonical

end HiddenDAGComponentFamilyCompilation
end Examples
end Causality
end Thesis
