import Thesis.Causality.Identification

namespace Thesis
namespace Causality

open Probability

/-!
# Constructively locating an actual separated conditional kernel cell

A conditional counterexample stores failure of agreement on common support.
It does not directly return an assignment or a rational gap as data.  Under
observational positivity every reference cell has an explicitly constructed
positive supported value.  Comparing those finite rational values therefore
gives a Boolean predicate on the signature's actual assignment enumeration.

The finite search below returns its first separated cell.  In the exhausted
branch, all checked values agree and hence the two original kernels agree,
contradicting the counterexample.  No propositional existential is eliminated
into a chosen assignment, and no arbitrary excluded-middle principle is used.
This lets subsequent semantic constructions consume an existing countermodel
without requesting a new hand-supplied source reference or numerical gap.
-/

/-- One actual separated cell of a conditional countermodel, with the two
supported rational values and the assignment retained as inspectable data. -/
structure ConditionalCounterexampleCell {S : ObservedSignature} (query : ConditionalKernelQuery S)
    (left right : ExactModel S) where
  reference : S.Assignment
  leftValue : ProbabilityResult.PositiveSupportedValue (query.sourceTerm.denote left reference)
  rightValue : ProbabilityResult.PositiveSupportedValue (query.sourceTerm.denote right reference)
  separated : Not (QProb.Equiv leftValue.value rightValue.value)

/-- Extract a separated reference from any counterexample in a model class
whose members are observationally positive.  Class membership and the models
are unchanged; only the finite kernel comparison is inspected. -/
noncomputable def ConditionalCounterexampleIn.separatedCell
    {S : ObservedSignature} {graph : ObservedGraph S} {C : GraphModelClass graph}
    {query : ConditionalKernelQuery S}
    (counterexample : ConditionalCounterexampleIn C query)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model) :
    ConditionalCounterexampleCell query counterexample.left counterexample.right := by
  let leftAt := fun reference => (obsPositive counterexample.left_mem).kernelPositiveSupportedValue query.operationKernel reference
  let rightAt := fun reference => (obsPositive counterexample.right_mem).kernelPositiveSupportedValue query.operationKernel reference
  let test := fun reference => decide (Not (QProb.Equiv (leftAt reference).value (rightAt reference).value))
  cases found : S.assignmentEnumeration.find? test with
  | some reference =>
      have checked : test reference = true := List.find?_some found
      exact ⟨reference, leftAt reference, rightAt reference, of_decide_eq_true checked⟩
  | none =>
      apply False.elim
      apply counterexample.query_separated
      intro reference _leftSupported _rightSupported
      have excluded := (List.find?_eq_none.mp found) reference (S.assignmentEnumeration_complete reference)
      have equal : QProb.Equiv (leftAt reference).value (rightAt reference).value := by
        -- This case split uses only decidable natural cross-products, not
        -- excluded middle for the semantic identifiability proposition.
        by_cases checked : QProb.Equiv (leftAt reference).value (rightAt reference).value
        · exact checked
        · exact False.elim (excluded (decide_eq_true checked))
      exact ⟨ProbabilityResult.trans (leftAt reference).equivalent
        (ProbabilityResult.trans (.value equal) (ProbabilityResult.symm (rightAt reference).equivalent))⟩

end Causality
end Thesis
