import Thesis.CausalTransport.BoundedNativeConditionalSearch
import Thesis.Examples.BoundedNativeClassification

namespace Thesis.Causality.Examples.BoundedNativeConditionalSearch

open Probability BoundedNativeSearch BoundedNativeClassification
open Causality.BoundedNativeSearch Causality.BoundedNativeConditionalSearch

/-!
# Conditional support and value regression at a null factual action

Reuse the actual binary `X -> Y` models with factual point mass at `(0, 0)`.
After `do(X = 1)`, the constant-zero model has null evidence `Y = 1` and the
copying model has positive evidence. Conditioning a certain event on that
evidence has value one in every supported model. The full bounded checker
must therefore return both a null-evidence witness and an attained common
supported value, rather than conflating support failure with value ambiguity.

Additional tests cover uniformly null evidence, uniformly positive evidence
with genuinely different conditional values, and an incompatible bounded
class. Whole-class tests inspect only the output's proved obligations; they
never expand the full catalogue in the kernel. Tiny finite-list tests execute
the recursion separately, including both orders of the mixed-support pair.
-/

def mixed : NativeConditionalQuery signature := ⟨effect.intervention, outcome, topEvent⟩
def certain : NativeConditionalQuery signature := ⟨effect.intervention, topEvent, outcome⟩
def impossibleEvidence : NativeConditionalQuery signature := ⟨effect.intervention, bottomEvent, outcome⟩

theorem mixed_null : ((entry false).model.interventionalValue mixed.intervention mixed.evidence).num = 0 := by decide +kernel
theorem mixed_positive : mixed.Supported (entry true).model := by decide +kernel
theorem mixed_not_supported : ¬ mixed.Supported (entry false).model := by decide +kernel

theorem certain_positive (original : FiniteHiddenDAGSCM signature projection) : certain.Supported original := by
  change 0 < FiniteProbRecord.eventMass (original.interventionalDist certain.intervention).atoms topEvent
  rw [FiniteProbRecord.eventMass_top, (original.interventionalDist certain.intervention).total_mass]
  exact (original.interventionalDist certain.intervention).den_pos

theorem impossible_unsupported (original : FiniteHiddenDAGSCM signature projection) :
    ¬ impossibleEvidence.Supported original := by
  intro positive
  change 0 < FiniteProbRecord.eventMass (original.interventionalDist impossibleEvidence.intervention).atoms (fun _ => false) at positive
  rw [FiniteProbRecord.eventMass_false] at positive
  exact Nat.lt_irrefl 0 positive

theorem mixed_value_one (original : FiniteHiddenDAGSCM signature projection) (positive : mixed.Supported original) :
    QProb.Equiv (mixed.value original positive) QProb.one :=
  (original.interventionalDist mixed.intervention).conditionOn_normalization mixed.evidence positive

theorem certain_different :
    ¬ QProb.Equiv (certain.value (entry false).model (certain_positive _))
      (certain.value (entry true).model (certain_positive _)) := by decide +kernel

def supportTag {query : NativeConditionalQuery signature} {candidates : List (NativeTemplateInstance projection)} :
    NativeTemplateInstance.ConditionalSupportInspection query candidates → Nat
  | .allSupported _ => 0
  | .nullWitness _ _ _ => 1

def valueTag {query : NativeConditionalQuery signature} {candidates : List (NativeTemplateInstance projection)} :
    NativeTemplateInstance.ConditionalValueInspection query candidates → Nat
  | .unsupported _ => 0
  | .identified _ _ _ _ => 1
  | .ambiguous _ _ _ _ _ _ _ => 2

theorem inspect_empty_values :
    valueTag (NativeTemplateInstance.inspectValues mixed ([] : List (NativeTemplateInstance projection))) = 0 := rfl
theorem inspect_null_values :
    valueTag (NativeTemplateInstance.inspectValues mixed [entry false]) = 0 := by decide +kernel
theorem inspect_mixed_support :
    supportTag (NativeTemplateInstance.inspectSupport mixed [entry false, entry true]) = 1 := by decide +kernel
theorem inspect_mixed_values :
    valueTag (NativeTemplateInstance.inspectValues mixed [entry false, entry true]) = 1 := by decide +kernel
theorem inspect_mixed_values_reversed :
    valueTag (NativeTemplateInstance.inspectValues mixed [entry true, entry false]) = 1 := by decide +kernel
theorem inspect_equal_supported_values :
    valueTag (NativeTemplateInstance.inspectValues mixed [entry true, entry true]) = 1 := by decide +kernel
theorem inspect_different_supported_values :
    valueTag (NativeTemplateInstance.inspectValues certain [entry false, entry true]) = 2 := by decide +kernel

/-- Public tags distinguish incompatibility from compatibility with no
supported conditional. They are regression helpers, not replacement semantics. -/
def compatibilityTag {denominatorBound : Nat} {query : NativeConditionalQuery signature} :
    Causality.BoundedNativeConditionalSearch.Result projection 2 1 denominatorBound observed query → Nat
  | .incompatible _ => 0
  | .compatible _ _ _ => 1

def resultSupportTag {denominatorBound : Nat} {query : NativeConditionalQuery signature} :
    Causality.BoundedNativeConditionalSearch.Result projection 2 1 denominatorBound observed query → Nat
  | .incompatible _ => 0
  | .compatible _ (.allSupported _) _ => 1
  | .compatible _ (.nullWitness _ _) _ => 2

def resultValueTag {denominatorBound : Nat} {query : NativeConditionalQuery signature} :
    Causality.BoundedNativeConditionalSearch.Result projection 2 1 denominatorBound observed query → Nat
  | .incompatible _ => 0
  | .compatible _ _ (.unsupported _) => 1
  | .compatible _ _ (.identified _ _) => 2
  | .compatible _ _ (.ambiguous _ _ _) => 3

theorem complete_class_mixed_support
    (answer : Causality.BoundedNativeConditionalSearch.Result projection 2 1 1 observed mixed) :
    resultSupportTag answer = 2 := by
  cases answer with
  | incompatible noMatch => exact False.elim (noMatch ⟨(entry false).model, entry_fits false⟩)
  | compatible witness support values =>
      cases support with
      | allSupported positive => exact False.elim (mixed_not_supported (positive (entry false).model (entry_fits false)))
      | nullWitness _ _ => rfl

theorem complete_class_mixed_value
    (answer : Causality.BoundedNativeConditionalSearch.Result projection 2 1 1 observed mixed) :
    resultValueTag answer = 2 := by
  cases answer with
  | incompatible noMatch => exact False.elim (noMatch ⟨(entry false).model, entry_fits false⟩)
  | compatible witness support values =>
      cases values with
      | unsupported noSupport => exact False.elim (noSupport (entry true).model (entry_fits true) mixed_positive)
      | identified _ _ => rfl
      | ambiguous left right different =>
          exact False.elim (different (QProb.equiv_trans (mixed_value_one _ left.supported)
            (QProb.equiv_symm (mixed_value_one _ right.supported))))

theorem complete_class_null_value
    (answer : Causality.BoundedNativeConditionalSearch.Result projection 2 1 1 observed impossibleEvidence) :
    compatibilityTag answer = 1 ∧ resultValueTag answer = 1 := by
  cases answer with
  | incompatible noMatch => exact False.elim (noMatch ⟨(entry false).model, entry_fits false⟩)
  | compatible witness support values =>
      cases values with
      | unsupported _ => exact ⟨rfl, rfl⟩
      | identified witness _ => exact False.elim (impossible_unsupported _ witness.supported)
      | ambiguous left _ _ => exact False.elim (impossible_unsupported _ left.supported)

theorem complete_class_certain_support
    (answer : Causality.BoundedNativeConditionalSearch.Result projection 2 1 1 observed certain) :
    resultSupportTag answer = 1 := by
  cases answer with
  | incompatible noMatch => exact False.elim (noMatch ⟨(entry false).model, entry_fits false⟩)
  | compatible witness support values =>
      cases support with
      | allSupported _ => rfl
      | nullWitness witness nullEvidence =>
          have positive := (certain.supported_iff_num_pos witness.entry.model).mp (certain_positive _)
          rw [nullEvidence] at positive
          exact False.elim (Nat.lt_irrefl 0 positive)

theorem complete_class_certain_ambiguous
    (answer : Causality.BoundedNativeConditionalSearch.Result projection 2 1 1 observed certain) :
    resultValueTag answer = 3 := by
  cases answer with
  | incompatible noMatch => exact False.elim (noMatch ⟨(entry false).model, entry_fits false⟩)
  | compatible witness support values =>
      cases values with
      | unsupported noSupport => exact False.elim (noSupport (entry false).model (entry_fits false) (certain_positive _))
      | identified witness constant =>
          have left := constant (entry false).model (entry_fits false) (certain_positive _)
          have right := constant (entry true).model (entry_fits true) (certain_positive _)
          exact False.elim (certain_different (QProb.equiv_trans left (QProb.equiv_symm right)))
      | ambiguous _ _ _ => rfl

theorem zero_bound_incompatible
    (answer : Causality.BoundedNativeConditionalSearch.Result projection 2 1 0 observed mixed) :
    compatibilityTag answer = 0 := by
  cases answer with
  | incompatible _ => rfl
  | compatible witness _ _ =>
      exact False.elim ((Nat.not_le_of_lt (witness.entry.factors x).den_pos) (witness.denominators x))

theorem solver_mixed_support :
    resultSupportTag (Causality.BoundedNativeConditionalSearch.solve projection 2 1 1 observed mixed) = 2 :=
  complete_class_mixed_support _
theorem solver_mixed_value :
    resultValueTag (Causality.BoundedNativeConditionalSearch.solve projection 2 1 1 observed mixed) = 2 :=
  complete_class_mixed_value _
theorem solver_null_value :
    let answer := Causality.BoundedNativeConditionalSearch.solve projection 2 1 1 observed impossibleEvidence
    compatibilityTag answer = 1 ∧ resultValueTag answer = 1 := complete_class_null_value _
theorem solver_certain_support :
    resultSupportTag (Causality.BoundedNativeConditionalSearch.solve projection 2 1 1 observed certain) = 1 :=
  complete_class_certain_support _
theorem solver_certain_ambiguous :
    resultValueTag (Causality.BoundedNativeConditionalSearch.solve projection 2 1 1 observed certain) = 3 :=
  complete_class_certain_ambiguous _
theorem solver_zero_bound_incompatible :
    compatibilityTag (Causality.BoundedNativeConditionalSearch.solve projection 2 1 0 observed mixed) = 0 :=
  zero_bound_incompatible _

end Thesis.Causality.Examples.BoundedNativeConditionalSearch
