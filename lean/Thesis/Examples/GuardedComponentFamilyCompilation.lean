import Thesis.CausalTransport.GuardedComponentFamilyCompilation
import Thesis.Examples.GuardedComponentCompilation

namespace Thesis
namespace Causality
namespace Examples
namespace ZeroCellComponentFamilyCompilation

open Probability ZeroCellChain ZeroCellLocalIdentification

/-!
# A whole host stays supported when a later component input is undefined

Use the actual nonpositive two-node SCM, with constant `X = false` and an
unbiased private `Y`.  The `{X}` input is the independently action-deleted
compound marginal from the reverse-bridge regression.  The `{Y}` input is
the earlier guarded component extraction, retaining its host quotient.
At the reference `X = true`, the first input has value zero and the second
has no value because that host quotient divides by a null `X` cylinder.

The whole-host family fold nevertheless has a complete ordinary support tree
and a present zero.  Both `X` prefix guards are zero before `Y`, so no `Y`
input support, marginal subtree or positive denominator is supplied.  The
strict product of these same recursive component formulas remains undefined.
This deliberately prevents mistaking guarded host assembly for an unchecked
rearrangement into the positive engine's older strict-product syntax.
-/

private def xComponent : NodeSet signature := ZeroCellReverseComponentCompilation.component
private def yComponent : NodeSet signature := ZeroCellComponentCompilation.component

private theorem partition_eq : graph.cComponents NodeSet.full = [xComponent, yComponent] := by
  decide +kernel

/-- The total map keeps the actual compound inputs, not fresh observational
factor kernels.  Only the two listed components are used by the compiler. -/
private noncomputable def recursiveFormula (component : NodeSet signature) : ProbabilityTerm signature :=
  if NodeSet.equal component xComponent = true then ZeroCellReverseComponentCompilation.componentInput.formula
  else ZeroCellGuardedComponent.gappedReduction.formula

/-- Finite Boolean component classification constructs data in `Type`.
The second-case equality is proved inside `Prop`; no certificate is chosen
from a propositional existence or disjunction.  Endpoint reindexing leaves
the input's inner derivation inspectable. -/
private noncomputable def recursiveReduction (component : NodeSet signature)
    (listed : component ∈ graph.cComponents NodeSet.full) :
    PublishedCurrentKernelReduction graph component (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full component)) := by
  if isX : NodeSet.equal component xComponent = true then
    have same := (NodeSet.equal_eq_true_iff _ _).mp isX
    exact {
      formula := ZeroCellReverseComponentCompilation.componentInput.formula
      actionFree := ZeroCellReverseComponentCompilation.componentInput.actionFree
      derivation := DoCalculusDerivation.eqCongr (G := graph) (separation := pathRuleSeparation graph)
        (by rw [same]; rfl) rfl ZeroCellReverseComponentCompilation.componentInput.derivation
    }
  else
    have same : component = yComponent := by
      rw [partition_eq] at listed
      rcases List.mem_cons.mp listed with first | later
      · exact False.elim (isX ((NodeSet.equal_eq_true_iff _ _).mpr first))
      · rcases List.mem_cons.mp later with second | absent
        · exact second
        · exact False.elim (List.not_mem_nil absent)
    exact {
      formula := ZeroCellGuardedComponent.gappedReduction.formula
      actionFree := ZeroCellGuardedComponent.gappedReduction.actionFree
      derivation := DoCalculusDerivation.eqCongr (G := graph) (separation := pathRuleSeparation graph)
        (by rw [same]; rfl) rfl ZeroCellGuardedComponent.gappedReduction.derivation
    }

private theorem recursiveReduction_formula (component : NodeSet signature)
    (listed : component ∈ graph.cComponents NodeSet.full) :
    (recursiveReduction component listed).formula = recursiveFormula component := by
  unfold recursiveReduction recursiveFormula
  split <;> rfl

noncomputable def family : PublishedComponentKernelReductionFamily graph NodeSet.full NodeSet.empty :=
  ⟨recursiveFormula, recursiveReduction, recursiveReduction_formula⟩

/-- Only `{X}` input variants are ever demanded at this reference.  Their
whole reindexing and compound marginal trees are supplied explicitly. -/
private noncomputable def xInput_supported (component : NodeSet signature)
    (listed : component ∈ graph.cComponents NodeSet.full)
    (isX : NodeSet.equal component xComponent = true) (variant : signature.Assignment) :
    LocalDerivationSupport model variant ((recursiveReduction component listed).derivation.compile graph.dSeparationCorrectness) := by
  let inner := ZeroCellReverseComponentCompilation.componentInput_supported variant
  let source := Kernel.unconditional_supportedAt model component
    (NodeSet.union NodeSet.empty (NodeSet.diff NodeSet.full component)) variant
  dsimp [recursiveReduction, PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  simp only [isX, dif_pos]
  exact ⟨source, ⟨inner.endpoints.2, inner⟩⟩

private noncomputable def firstInputs :
    ComponentFamilyFactorInputs family graph.dSeparationCorrectness model reference x (by rfl) where
  componentSupported := Kernel.supportedAt_of_observational_overlap model _ reference (by
    unfold ObservationalCylinderPositiveAt
    decide +kernel)
  overlap := by unfold ObservationalCylinderPositiveAt; decide +kernel
  numeratorInputSupport := fun variant _listed =>
    xInput_supported (graph.componentAt NodeSet.full x) (graph.componentAt_spec NodeSet.full x rfl).1
      (by decide +kernel) variant
  denominatorInputSupport := fun variant _listed =>
    xInput_supported (graph.componentAt NodeSet.full x) (graph.componentAt_spec NodeSet.full x rfl).1
      (by decide +kernel) variant
  denominatorPositive := by
    refine ⟨QProb.one, .value ?_, ?_⟩ <;> decide +kernel

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

/-- The later factor receives no data: both its causal and displayed host
prefixes are actually zero.  The impossible positive witness is eliminated
using explicit finite rational values, not arbitrary excluded middle. -/
private noncomputable def conditions :
    ComponentFamilySupportConditions family graph.dSeparationCorrectness model reference := by
  intro node _selected branch
  if atFirst : node.val = 0 then
    have same : node = x := Fin.ext atFirst
    subst node
    exact firstInputs
  else
    have bound : node.val < 2 := node.isLt
    have atSecond : node.val = 1 := by omega
    have same : node = y := Fin.ext atSecond
    subst node
    cases branch with
    | inl sourcePositive =>
        have zero : ((ProbabilityTerm.kernel ⟨chainPrefix NodeSet.full y.val, NodeSet.empty, NodeSet.empty⟩).denote
            model reference).map (fun value => value.num) = some 0 := by
          decide +kernel
        exact False.elim (positive_impossible_of_zero zero sourcePositive)
    | inr targetPositive =>
        have zero : ((GuardedHostChain.prefixTerm NodeSet.full family.factor y.val (Nat.le_of_lt y.isLt)).denote
            model reference).map (fun value => value.num) = some 0 := by
          decide +kernel
        exact False.elim (positive_impossible_of_zero zero targetPositive)

noncomputable def reduction := family.guardedReduction (ObservedGraph.KernelHostClosed.full graph)

noncomputable def supported : LocalDerivationSupport model reference
    (reduction.derivation.compile graph.dSeparationCorrectness) :=
  family.guardedReduction_supportedAt graph.dSeparationCorrectness (ObservedGraph.KernelHostClosed.full graph)
    model reference conditions

noncomputable def sound : ProbabilityTerm.EquivalentAt model
    (.kernel ⟨NodeSet.full, NodeSet.empty, NodeSet.empty⟩) reduction.formula reference :=
  (reduction.derivation.compile graph.dSeparationCorrectness).denotational_soundAt
    (graph.publishedSoundness.primitive model compatible) supported

theorem guarded_host_is_supported_zero : (reduction.formula.denote model reference).map (fun value => value.num) = some 0 := by
  decide +kernel

theorem later_component_input_is_undefined :
    ((family.formula yComponent).denote model reference).isNone = true := by
  decide +kernel

theorem skipped_component_quotient_is_undefined : ((family.factor y).denote model reference).isNone = true := by
  decide +kernel

theorem strict_component_product_is_undefined :
    ((productTerms ((graph.cComponents NodeSet.full).map family.formula)).denote model reference).isNone = true := by
  decide +kernel

end ZeroCellComponentFamilyCompilation
end Examples
end Causality
end Thesis
