import Thesis.CausalTransport.GuardedComponentCompilation
import Thesis.Examples.SupportAwareKernelCompilation

namespace Thesis
namespace Causality
namespace Examples
namespace ZeroCellGuardedComponent

open Probability ZeroCellChain ZeroCellLocalIdentification ZeroCellKernelCompilation

/-!
# A whole guarded component fold skips an undefined zero-prefix factor

Use the two-node nonpositive SCM with constant `X = false` and unbiased `Y`.
The full host is a bidirected-closed union of its two components, which is
admitted by the general extraction theorem.  At `X = true`, the first host
quotient is a supported zero and the second is undefined.

Both source and displayed `X` prefixes have zero mass.  The branch-local
conditions therefore supply no `Y` quotient support, overlap, denominator or
input subtrees.  Nevertheless the whole-component reduction has a complete
ordinary support tree and is interpreted by the existing soundness theorem.
This is a test of the actual generated current-input formula, not of a
mock weighted product of literal probabilities.
-/

private def component : NodeSet signature := NodeSet.full

private theorem component_subset : NodeSet.Subset component NodeSet.full :=
  fun _node _selected => rfl

private theorem component_bidirected_closed : forall {source target}, component source = true →
    (NodeSet.full : NodeSet signature) target = true → graph.bidirected source target = true →
    component target = true := fun _ _ _ => rfl

/-- A positive displayed value cannot represent a result whose present
numerator is zero.  The argument reads the explicit rational witness; it
does not choose a value or decide an arbitrary semantic proposition. -/
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

/-- The only needed quotient inputs are those for the first vertex.  Its
outcome numerator is zero, while its empty-prefix denominator is one. -/
private noncomputable def firstInputs :
    GuardedComponentFactorInputs input graph.dSeparationCorrectness model reference x where
  overlap := by unfold ObservationalCylinderPositiveAt; decide +kernel
  numeratorInputSupport := fun variant _listed => input_supported variant
  denominatorInputSupport := fun variant _listed => input_supported variant
  denominatorPositive := first_denominator_positive

/-- At the second position, both guards are genuinely zero in the actual
SCM and generated prefix formula.  No second-factor support is asserted. -/
private noncomputable def conditions :
    GuardedComponentSupportConditions input graph.dSeparationCorrectness component model reference := by
  intro node _inside branch
  have earlier : node.val = 0 ∨ node.val = 1 := by omega
  cases earlier with
  | inl atFirst =>
      have same : node = x := Fin.ext atFirst
      subst node
      exact firstInputs
  | inr atSecond =>
      have same : node = y := Fin.ext atSecond
      subst node
      cases branch with
      | inl sourcePositive =>
          have zero : ((ProbabilityTerm.kernel
              ⟨chainPrefix component y.val, componentExternalAction NodeSet.full NodeSet.empty component,
                NodeSet.empty⟩).denote model reference).map (fun value => value.num) = some 0 := by
            decide +kernel
          exact False.elim (positive_impossible_of_zero zero sourcePositive)
      | inr targetPositive =>
          have zero : ((guardedComponentPrefixTerm NodeSet.full input.formula component y.val
              (Nat.le_of_lt y.isLt)).denote model reference).map (fun value => value.num) = some 0 := by
            decide +kernel
          exact False.elim (positive_impossible_of_zero zero targetPositive)

noncomputable def reduction := input.guardedComponent component (ObservedGraph.KernelHostClosed.full graph)
  component_subset component_bidirected_closed

/-- The entire generated guarded fold is supported despite its missing
second quotient; the full inductively assembled support tree is retained. -/
noncomputable def supported : LocalDerivationSupport model reference
    (reduction.derivation.compile graph.dSeparationCorrectness) :=
  input.guardedComponent_supportedAt graph.dSeparationCorrectness component
    (ObservedGraph.KernelHostClosed.full graph) component_subset component_bidirected_closed
    model reference conditions

noncomputable def sound : ProbabilityTerm.EquivalentAt model
    (.kernel ⟨component, componentExternalAction NodeSet.full NodeSet.empty component, NodeSet.empty⟩)
    reduction.formula reference :=
  (reduction.derivation.compile graph.dSeparationCorrectness).denotational_soundAt
    (graph.publishedSoundness.primitive model compatible) supported

/-- The actual final formula has a present zero rather than a missing result. -/
theorem guarded_product_is_supported_zero :
    (reduction.formula.denote model reference).map (fun value => value.num) = some 0 := by
  decide +kernel

/-- The skipped quotient itself remains undefined.  The guarded compiler
has not replaced it with an arbitrary conditional value. -/
theorem skipped_factor_remains_undefined :
    (chainFactorFrom NodeSet.full input.formula y).denote model reference = none :=
  second_factor_at_null_prefix_is_undefined

end ZeroCellGuardedComponent
end Examples
end Causality
end Thesis
