import Thesis.CausalTransport.NativeTargetRecognition
import Thesis.Examples.NativeDemandEncoding

namespace Thesis.Causality.Examples.NativeTargetRecognition

open Probability NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping Thesis.Causality.NativeDemandEncoding

/-!
# Target recognition at null references and unused branches

The three-valued native fixture distinguishes native support from observed
availability. Inactive native cells do not turn an unavailable observational
conditional into a formula value. A zero weight can suppress that conditional's
support obligation, but cannot suppress malformed annotations or actionful
syntax. Conflicting causal profiles are still checked individually.

The general state equalities are also exercised inside nested literal frames.
No state catalogue, formula enumeration, reachability search or runtime solver
pilot is executed here. The finite-carrier example uses its membership theorem.
-/

def requested : Demand family := NativeDemandEncoding.atNull
def nowhere : Demand family := fun _ _ => false
def observed : FiniteProbRecord signature.Assignment := entry.uniformSupport.model.observationalDist
def pattern : signature.Assignment → Bool := observed.support

theorem available_unit_is_accepted :
    NativeTargetRecognition.recognize pattern requested (reference 2) (Term.encode family unitTerm requested) = true := by
  decide +kernel

/-- Empty native demands remain unused applications. The independent
observational evaluation must still exist at the requested reference. -/
theorem empty_demand_does_not_supply_availability :
    check family nullConditional nowhere = true ∧
      (Term.encode family nullConditional nowhere).checkAnnotations nowhere = true ∧
      NativeTargetRecognition.recognize pattern nowhere (reference 2) (Term.encode family nullConditional nowhere) = false ∧
      NativeTargetRecognition.recognize pattern nowhere (reference 2) (Term.encode family unitTerm nowhere) = true := by
  decide +kernel

theorem zero_weight_and_strict_boundaries :
    NativeTargetRecognition.recognize pattern requested (reference 2) NativeDemandEncoding.zeroWeight = true ∧
      NativeTargetRecognition.recognize pattern requested (reference 2)
        (Term.encode family (.multiply .zero nullConditional) requested) = false ∧
      NativeTargetRecognition.recognize pattern requested (reference 2)
        (Term.encode family (.weightedMultiply nullConditional .zero) requested) = false := by
  decide +kernel

theorem malformed_unused_annotations_are_rejected :
    check family NativeDemandEncoding.malformedSkippedFactor.erase requested = true ∧
      NativeTargetRecognition.recognize pattern requested (reference 2) NativeDemandEncoding.malformedSkippedFactor = false := by
  decide +kernel

/-- The observational status is a defined zero, yet the syntactic action
bit still refuses a formula containing an intervention in the unused child. -/
theorem unused_actions_are_rejected :
    (NativeDemandEncoding.hiddenAction.supportStatus pattern (reference 2)).isDefined = true ∧
      NativeTargetRecognition.recognize pattern requested (reference 2)
        (Term.encode family NativeDemandEncoding.hiddenAction requested) = false := by
  decide +kernel

theorem substitutions_and_denominators_are_checked :
    NativeTargetRecognition.recognize pattern (atReference (reference 0)) (reference 0)
      (Term.encode family (.evaluateAt (reference 2) nullConditional) (atReference (reference 0))) = false ∧
      NativeTargetRecognition.recognize pattern (atReference (reference 0)) (reference 0)
        (Term.encode family (.marginalize NodeSet.full nullConditional) (atReference (reference 0))) = false ∧
      NativeTargetRecognition.recognize pattern requested (reference 2)
        (Term.encode family (.divide unitTerm .zero) requested) = false := by
  decide +kernel

/-- Availability of a candidate never supplies support of a separate
causal source. The accepted unit does not repair the null query. -/
theorem source_support_is_separate :
    check family nullConditional requested = false ∧
      NativeTargetRecognition.recognize pattern requested (reference 2) (Term.encode family unitTerm requested) = true := by
  decide +kernel

def fullObserved : FiniteProbRecord signature.Assignment := fullSupport.model.observationalDist

theorem conflicting_native_profiles_are_not_merged :
    NativeTargetRecognition.recognize fullObserved.support (nullInProfiles (fun index => decide (index.val = 0))) (reference 2)
      (Term.encode conflicting (.kernel carrier) (nullInProfiles (fun index => decide (index.val = 0)))) = true ∧
      NativeTargetRecognition.recognize fullObserved.support (nullInProfiles (fun index => decide (index.val = 1))) (reference 2)
        (Term.encode conflicting (.kernel carrier) (nullInProfiles (fun index => decide (index.val = 1)))) = false := by
  decide +kernel

theorem malformed_arity_is_refused :
    (NativeTargetRecognition.transition pattern (.multiply requested) []).isSome = false ∧
      (NativeTargetRecognition.transition pattern (.zero requested)
        [NativeTargetRecognition.State.zero requested]).isSome = false := ⟨rfl, rfl⟩

example (term : Term family) :
    NativeTargetRecognition.transition pattern term.label
      (term.children.map (NativeTargetRecognition.summarize pattern)) =
        some (NativeTargetRecognition.summarize pattern term) := NativeTargetRecognition.transition_summarize pattern term

example (term : Term family) :
    NativeTargetRecognition.summarize pattern term ∈ NativeTargetRecognition.State.enumeration family :=
  NativeTargetRecognition.summarize_mem pattern term

/-- The whole state is preserved, including a literal null sibling and
denominator. This is a recognizer congruence, not a causal proof inferred
from matching metadata; it also covers contexts that are rejected on both sides. -/
theorem nested_ac_invariance (first second third : Term family) :
    NativeTargetRecognition.recognize pattern requested (reference 2)
      (([Frame.weightedRight requested (.zero requested), Frame.divideLeft requested (Term.encode family unitTerm requested),
        Frame.addRight requested (Term.encode family nullConditional requested)]).foldr Frame.fill
          (.multiply requested (.multiply requested first second) third)) =
    NativeTargetRecognition.recognize pattern requested (reference 2)
      (([Frame.weightedRight requested (.zero requested), Frame.divideLeft requested (Term.encode family unitTerm requested),
        Frame.addRight requested (Term.encode family nullConditional requested)]).foldr Frame.fill
          (.multiply requested first (.multiply requested second third))) :=
  NativeTargetRecognition.recognize_context_congr pattern requested (reference 2) _
    (NativeTargetRecognition.summarize_multiply_assoc pattern requested first second third)

end Thesis.Causality.Examples.NativeTargetRecognition
