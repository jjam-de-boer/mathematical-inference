import Thesis.CausalTransport.HiddenDAGKernelCompilation
import Thesis.Examples.HiddenDAGIdentification

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGKernelCompilation

open Probability HiddenDAGCollapse

/-!
# Native local input compilation with a noncanonical collapse and zeros

Reuse the original five-node hidden relay, not its positive mechanism variant.
Its observed `Y = true` event is null and its collapse has a three-child root.
The current observational input and its `Y` marginal nevertheless have native
recursive support.  Existing native soundness interprets the actual marginal
derivation in that full-DAG model without a canonical-membership proof.

The `Y` prefix quotient is checked as well.  Its displayed denominator is
the positive `X = true` cylinder while its `Y = true` numerator is zero.
All native input subtrees are supplied by the general zero-permitting
initializer.  Only the small original fixture's denominator is numerically
checked; construction of the support trees uses the general theorems.
-/

def input : PublishedCurrentKernelReduction projection.observedGraph NodeSet.full NodeSet.empty :=
  PublishedCurrentKernelReduction.observational projection.observedGraph

noncomputable def input_supported (reference : signature.Assignment) :
    HiddenDAGLocalDerivationSupport model reference
      (input.derivation.compile projection.observedGraph.dSeparationCorrectness) :=
  PublishedCurrentKernelReduction.hiddenDAG_observational_supportedAt model reference

def yMarginal : PublishedCurrentKernelReduction projection.observedGraph
    (NodeSet.singleton y) NodeSet.empty :=
  input.marginal (NodeSet.singleton y) (NodeSet.disjoint_empty_left _)
    (fun _node _selected => rfl)

/-- The reference has zero mass for the requested outcome, but the native
unconditional marginal and its full recursive derivation remain supported. -/
noncomputable def zero_marginal_supported :
    HiddenDAGLocalDerivationSupport model HiddenDAGSoundness.reference
      (yMarginal.derivation.compile projection.observedGraph.dSeparationCorrectness) :=
  input.hiddenDAG_marginal_supportedAt (NodeSet.singleton y) (NodeSet.disjoint_empty_left _)
    (fun _node _selected => rfl) model HiddenDAGSoundness.reference
    (fun variant _listed => input_supported variant)

noncomputable def zero_marginal_sound : model.TermEquivalentAt
    (.kernel ⟨NodeSet.singleton y, NodeSet.empty, NodeSet.empty⟩)
    yMarginal.formula HiddenDAGSoundness.reference :=
  (yMarginal.derivation.compile projection.observedGraph.dSeparationCorrectness).hiddenDAG_denotational_soundAt
    zero_marginal_supported

/-- Local positivity of this displayed denominator is checked directly in
the original finite record.  The full observed law remains nonpositive. -/
def denominator_positive : ProbabilityResult.PositiveSupportedValue
    (model.termDenote
      (.marginalize (NodeSet.diff (NodeSet.full : NodeSet signature) (chainCondition NodeSet.full y))
        input.formula) HiddenDAGSoundness.reference) := by
  refine ⟨⟨1, 2, by decide⟩, .value ?_, ?_⟩
  · decide +kernel
  · decide +kernel

/-- The native prefix factor is supported from this one denominator and
the enumerated native input subtrees.  Its outcome mass may still be zero. -/
noncomputable def zero_factor_supported :
    HiddenDAGLocalDerivationSupport model HiddenDAGSoundness.reference
      ((input.factorDerivation (NodeSet.disjoint_empty_left _) y rfl).compile
        projection.observedGraph.dSeparationCorrectness) := by
  let kernel : Kernel signature :=
    ⟨NodeSet.singleton y, NodeSet.empty, chainCondition NodeSet.full y⟩
  have source := model.kernelSupportedAt_of_observational_overlap kernel HiddenDAGSoundness.reference (by
    unfold FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt
    decide +kernel)
  exact input.hiddenDAG_factor_supportedAt (NodeSet.disjoint_empty_left _) y rfl
    model HiddenDAGSoundness.reference source (fun variant _listed => input_supported variant)
    (fun variant _listed => input_supported variant) denominator_positive

/-- Native soundness interprets the constructed zero-permitting prefix
derivation, without a canonical compatibility or positive-model premise. -/
noncomputable def zero_factor_sound : model.TermEquivalentAt
    (.kernel ⟨NodeSet.singleton y, NodeSet.empty, chainCondition NodeSet.full y⟩)
    (chainFactorFrom NodeSet.full input.formula y) HiddenDAGSoundness.reference :=
  ((input.factorDerivation (NodeSet.disjoint_empty_left _) y rfl).compile
    projection.observedGraph.dSeparationCorrectness).hiddenDAG_denotational_soundAt
      zero_factor_supported

/-- The tested original full-DAG model really is outside the positive
adapter's class.  This reuses the existing concrete null-cylinder proof. -/
theorem model_is_not_positive : ¬ model.ObservationallyPositive :=
  HiddenDAGIdentification.zero_model_not_positive

/-! ## Whole native component with a genuinely skipped final quotient -/

/-- The full host is bidirected-closed.  In this fixture its three observed
vertices share a collapsed root, but the constructor does not require a
canonical pair-root representation. -/
private theorem full_bidirected_closed : forall {source target},
    (NodeSet.full : NodeSet signature) source = true → NodeSet.full target = true →
    projection.observedGraph.bidirected source target = true → NodeSet.full target = true :=
  fun _ _ _ => rfl

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

/-- Only the first two host quotients need data: the `X` prefix is positive,
whereas adjoining the impossible `Y = true` outcome makes the next prefix
zero.  The actual `Z` quotient is therefore skipped on both branch guards. -/
private noncomputable def whole_conditions :
    HiddenDAGGuardedComponentSupportConditions input NodeSet.full model HiddenDAGSoundness.reference := by
  intro node _inside branch
  have position : node.val = 0 ∨ node.val = 1 ∨ node.val = 2 := by omega
  cases position with
  | inl atFirst =>
      have same : node = x := Fin.ext atFirst
      subst node
      refine ⟨?_, (fun variant _listed => input_supported variant),
        (fun variant _listed => input_supported variant), ?_⟩
      · unfold FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt
        decide +kernel
      · refine ⟨QProb.one, .value ?_, ?_⟩ <;> decide +kernel
  | inr later =>
      cases later with
      | inl atSecond =>
          have same : node = y := Fin.ext atSecond
          subst node
          refine ⟨?_, (fun variant _listed => input_supported variant),
            (fun variant _listed => input_supported variant), denominator_positive⟩
          unfold FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt
          decide +kernel
      | inr atThird =>
          have same : node = z := Fin.ext atThird
          subst node
          cases branch with
          | inl sourcePositive =>
              have zero : (model.termDenote
                  (.kernel ⟨chainPrefix NodeSet.full z.val,
                    componentExternalAction NodeSet.full NodeSet.empty NodeSet.full, NodeSet.empty⟩)
                  HiddenDAGSoundness.reference).map (fun value => value.num) = some 0 := by
                decide +kernel
              exact False.elim (positive_impossible_of_zero zero sourcePositive)
          | inr targetPositive =>
              have zero : (model.termDenote
                  (guardedComponentPrefixTerm NodeSet.full input.formula NodeSet.full z.val
                    (Nat.le_of_lt z.isLt)) HiddenDAGSoundness.reference).map (fun value => value.num) = some 0 := by
                decide +kernel
              exact False.elim (positive_impossible_of_zero zero targetPositive)

noncomputable def wholeComponent := input.guardedComponent NodeSet.full
  (ObservedGraph.KernelHostClosed.full projection.observedGraph)
  (fun _node selected => selected) full_bidirected_closed

/-- All required native subtrees are constructed by the general adapter;
no global positivity or support of the skipped `Z` quotient is asserted. -/
noncomputable def whole_component_supported : HiddenDAGLocalDerivationSupport model HiddenDAGSoundness.reference
    (wholeComponent.derivation.compile projection.observedGraph.dSeparationCorrectness) :=
  input.hiddenDAG_guardedComponent_supportedAt NodeSet.full
    (ObservedGraph.KernelHostClosed.full projection.observedGraph)
    (fun _node selected => selected) full_bidirected_closed model HiddenDAGSoundness.reference whole_conditions

noncomputable def whole_component_sound : model.TermEquivalentAt
    (.kernel ⟨NodeSet.full, componentExternalAction NodeSet.full NodeSet.empty NodeSet.full, NodeSet.empty⟩)
    wholeComponent.formula HiddenDAGSoundness.reference :=
  (wholeComponent.derivation.compile projection.observedGraph.dSeparationCorrectness).hiddenDAG_denotational_soundAt
    whole_component_supported

theorem whole_component_is_supported_zero :
    (model.termDenote wholeComponent.formula HiddenDAGSoundness.reference).map (fun value => value.num) = some 0 := by
  decide +kernel

/-- The compiler has not silently repaired the null conditional.  Its
displayed quotient remains undefined inside the supported guarded product. -/
theorem skipped_last_factor_is_undefined :
    (model.termDenote (chainFactorFrom NodeSet.full input.formula z) HiddenDAGSoundness.reference).isNone = true := by
  decide +kernel

end HiddenDAGKernelCompilation
end Examples
end Causality
end Thesis
