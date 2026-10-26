import Thesis.Causality.Semantics

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Exact evaluation from an observational table

Evaluate an action-free probability term against a finite observational
record. Syntax, partial arithmetic and the public name are those of the
ordinary term interpreter. Keeping the evaluator beside the ordinary
semantics avoids importing native hidden-DAG completeness merely to check
an observational numerical example.

Two bridges justify reusable finite-table computations. Action-free syntax
has literally the same result as ordinary SCM evaluation. Replacing a table
by one with equivalent event probabilities preserves the complete partial
result, including unsupported conditionals. Consequently a regression may
verify a model's finite observed table once rather than repeatedly reducing
its latent mechanisms beneath every sum and quotient. Neither bridge uses
do-calculus soundness, identification completeness or a selected formula.
-/

namespace ProbabilityTerm

/-- Evaluate syntax directly from an observational record.  Actionful kernel
leaves are rejected, rather than quietly reinterpreted as observational ones.
For certified action-free terms this is literally the native evaluation. -/
def observationalDenote (record : FiniteProbRecord S.Assignment) :
    ProbabilityTerm S → S.Assignment → ProbabilityResult.Result
  | .zero, _ => some QProb.zero
  | .kernel queryKernel, reference =>
      if queryKernel.hasAction then none else
        ProbabilityResult.divide (some (record.probVal (queryKernel.numeratorEvent reference)))
          (some (record.probVal (queryKernel.conditionEvent reference)))
  | .marginalize nodes inner, reference =>
      ProbabilityResult.sum ((marginalAssignments S nodes reference).map
        (fun variant => inner.observationalDenote record variant))
  | .evaluateAt fixed inner, _ => inner.observationalDenote record fixed
  | .add left right, reference => ProbabilityResult.add
      (left.observationalDenote record reference) (right.observationalDenote record reference)
  | .multiply left right, reference => ProbabilityResult.multiply
      (left.observationalDenote record reference) (right.observationalDenote record reference)
  | .weightedMultiply weight factor, reference => ProbabilityResult.weightedMultiply
      (weight.observationalDenote record reference) (factor.observationalDenote record reference)
  | .divide numerator denominator, reference => ProbabilityResult.divide
      (numerator.observationalDenote record reference) (denominator.observationalDenote record reference)

/-- Reading an action-free expression from the actual observed record agrees
literally with the finite latent SCM semantics, not merely at positive cells.
The action-free premise is essential: an observational table cannot in
general supply the meaning of an intervened kernel. -/
theorem observationalDenote_eq_scm (model : FiniteLatentSCM S)
    (term : ProbabilityTerm S) (actionFree : term.ActionFree) (reference : S.Assignment) :
    term.observationalDenote model.observationalDist reference = term.denote model reference := by
  induction term generalizing reference with
  | zero => rfl
  | kernel kernel =>
      have noAction := ProbabilityTerm.actionFree_hasAction_false kernel actionFree
      simp only [observationalDenote, denote, Kernel.denote, Kernel.distribution,
        noAction, Bool.false_eq_true, if_false]
  | marginalize nodes inner inductionHypothesis =>
      simp only [observationalDenote, denote]
      have same : (fun variant => inner.observationalDenote model.observationalDist variant) =
          (fun variant => inner.denote model variant) :=
        funext (inductionHypothesis actionFree)
      rw [same]
  | evaluateAt fixed inner inductionHypothesis => exact inductionHypothesis actionFree fixed
  | add left right leftIH rightIH =>
      simp only [observationalDenote, denote,
        leftIH actionFree.1 reference, rightIH actionFree.2 reference]
  | multiply left right leftIH rightIH =>
      simp only [observationalDenote, denote,
        leftIH actionFree.1 reference, rightIH actionFree.2 reference]
  | weightedMultiply weight factor weightIH factorIH =>
      simp only [observationalDenote, denote,
        weightIH actionFree.1 reference, factorIH actionFree.2 reference]
  | divide numerator denominator numeratorIH denominatorIH =>
      simp only [observationalDenote, denote,
        numeratorIH actionFree.1 reference, denominatorIH actionFree.2 reference]

/-- Equivalent observational records give equivalent partial results for
every expression. No action-free premise is needed here: both evaluations
reject an actionful leaf, and neither fills in an undefined conditional.
The finite syntax/list recursions construct the Type-valued evidence directly. -/
noncomputable def observationalDenote_congr
    (left right : FiniteProbRecord S.Assignment)
    (agree : forall event, QProb.Equiv (left.probVal event) (right.probVal event))
    (term : ProbabilityTerm S) (reference : S.Assignment) :
    ProbabilityResult.Equivalent
      (term.observationalDenote left reference) (term.observationalDenote right reference) := by
  induction term generalizing reference with
  | zero => exact ProbabilityResult.refl _
  | kernel kernel =>
      cases hasAction : kernel.hasAction with
      | false =>
          simp only [observationalDenote, hasAction, Bool.false_eq_true, if_false]
          exact ProbabilityResult.divide_congr
            (.value (agree (kernel.numeratorEvent reference)))
            (.value (agree (kernel.conditionEvent reference)))
      | true =>
          simp only [observationalDenote, hasAction, if_true]
          exact .unsupported
  | marginalize nodes inner inductionHypothesis =>
      simpa only [observationalDenote] using
        (ProbabilityResult.sum_map_congr (marginalAssignments S nodes reference)
          (fun variant => inner.observationalDenote left variant)
          (fun variant => inner.observationalDenote right variant) inductionHypothesis)
  | evaluateAt fixed inner inductionHypothesis => exact inductionHypothesis fixed
  | add first second firstIH secondIH =>
      exact ProbabilityResult.add_congr (firstIH reference) (secondIH reference)
  | multiply first second firstIH secondIH =>
      exact ProbabilityResult.multiply_congr (firstIH reference) (secondIH reference)
  | weightedMultiply weight factor weightIH factorIH =>
      exact ProbabilityResult.weightedMultiply_congr (weightIH reference) (factorIH reference)
  | divide numerator denominator numeratorIH denominatorIH =>
      exact ProbabilityResult.divide_congr (numeratorIH reference) (denominatorIH reference)

end ProbabilityTerm
end Causality
end Thesis
