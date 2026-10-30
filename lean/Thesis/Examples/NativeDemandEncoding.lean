import Thesis.CausalTransport.NativeDemandEncoding
import Thesis.Examples.NativeDemandTypes

namespace Thesis.Causality.Examples.NativeDemandEncoding

open Probability NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping
open Thesis.Causality.NativeDemandEncoding

/-!
# Faithful syntax and demand annotations at null references

The three-valued fixture has one declared null reference. These regressions
exercise canonical annotation checking, fixed/marginal demand transfer,
and the distinction between omitting a factor's support obligation and
deleting its syntax. In particular an actionful kernel under a zero weight
remains visible to the observational-formula check.

The finite alphabet count is small here. We do not enumerate complete
trees, contexts, or proof paths, and the quantified examples use the general
round-trip and support-agreement theorems rather than such a search.
-/

def atNull : Demand family := atReference (reference 2)
def nowhere : Demand family := fun _ _ => false
def nullKernel : Kernel signature := ⟨NodeSet.full, NodeSet.empty, NodeSet.full⟩

theorem alphabet_is_finite : (Symbol.enumeration family).length = 144 := by decide +kernel

def zeroWeight : Term family :=
  .weightedMultiply atNull (.zero atNull) (.kernel nowhere nullKernel)

theorem zero_weight_is_well_formed : zeroWeight.wellFormed = true := by decide +kernel

theorem zero_weight_is_canonical :
    Term.encode family (.weightedMultiply .zero nullConditional) atNull = zeroWeight :=
  (Term.wellFormed_iff zeroWeight).mp zero_weight_is_well_formed

theorem skipped_factor_remains_literal :
    zeroWeight.erase = .weightedMultiply .zero nullConditional := rfl

/-- An unused conditional is retained, while its genuine null support does
not prevent a defined zero-weight product from being accepted. -/
theorem zero_weight_support_boundary :
    zeroWeight.check = true ∧
      (Term.encode family (.multiply .zero nullConditional) atNull).check = false ∧
      (Term.encode family (.weightedMultiply unitTerm nullConditional) atNull).check = false := by decide +kernel

/-- Format coherence is checked even where numerical support is omitted.
Re-encoding the same erasure supplies the correct empty factor demand. -/
def malformedSkippedFactor : Term family :=
  .weightedMultiply atNull (.zero atNull) (.kernel atNull nullKernel)

theorem malformed_annotation_is_rejected :
    NativeDemandTyping.check family malformedSkippedFactor.erase atNull = true ∧
      malformedSkippedFactor.checkAnnotations atNull = false ∧
      malformedSkippedFactor.check = false := by decide +kernel

def hiddenAction : ProbabilityTerm signature :=
  .weightedMultiply .zero (.kernel ⟨NodeSet.empty, NodeSet.full, NodeSet.empty⟩)

theorem skipped_action_is_still_visible :
    (Term.encode family hiddenAction atNull).check = true ∧
      (Term.encode family hiddenAction atNull).actionFreeCheck = false := by decide +kernel

/-- Retaining literal fixed references and marginal masks keeps the null
cell in scope even when the outer request is observationally supported. -/
theorem null_substitutions_are_checked :
    (Term.encode family (.evaluateAt (reference 2) nullConditional) (atReference (reference 0))).check = false ∧
      (Term.encode family (.marginalize NodeSet.full nullConditional) (atReference (reference 0))).check = false := by decide +kernel

theorem multiplication_label_ignores_grades :
    (Term.encode family (.multiply .zero unitTerm) atNull).label = .multiply atNull ∧
      (Term.encode family (.multiply unitTerm unitTerm) atNull).label = .multiply atNull := ⟨rfl, rfl⟩

example (term : ProbabilityTerm signature) (requested : Demand family) :
    (Term.encode family term requested).erase = term := Term.erase_encode family term requested

example (term : ProbabilityTerm signature) (requested : Demand family) :
    (Term.encode family term requested).infer = NativeDemandTyping.infer family term requested :=
  Term.infer_encode family term requested

example (term : ProbabilityTerm signature) (requested : Demand family) :
    (Term.encode family term requested).label ∈ Symbol.enumeration family := Symbol.mem_enumeration _

end Thesis.Causality.Examples.NativeDemandEncoding
