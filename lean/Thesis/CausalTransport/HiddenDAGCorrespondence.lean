import Thesis.CausalTransport.HiddenDAGCompleteness
import Thesis.CausalTransport.HiddenDAGIdentification

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Soundness and completeness in the full finite hidden-DAG class

This is the integration boundary for the independently proved native
soundness and reverse-realization completeness directions.  The quantifier
is over every finite SCM record on the supplied original DAG, allowing any
finite hidden and private-noise domains, rather than over an arbitrarily
selected indexed family.  Observed alphabets remain fixed.

For strictly positive observed laws on value-rich signatures, joint ID and
conditional IDC succeed exactly when their original query is identifiable.
Success retains the literal engine output and its native interpretation;
failure constructs original-DAG countermodels; public termination excludes
the unfinished result.  Matching the computed three-constructor result is
constructive and does not decide semantic identifiability by excluded middle.

The semantic equivalences with the positive projected class follow the same
two proved directions.  They do not identify arbitrary full-model collapses
with canonical pairwise-root models, or inhabit an external projection
interface for arbitrary selected families.  Neither the engine equivalences
nor these semantic equivalences are asserted for the entire zero-permitting
class; that requires the separate support-aware compilation development.
-/

namespace HiddenDAGModelClass

/-- Literal successful joint ID identifies its query throughout the full
positive original-DAG class.  This uses native certificate soundness in the
two actual records, not canonical membership of their collapsed models. -/
theorem identifyJointKernel_identified (query : JointKernelQuery S)
    {term : ProbabilityTerm S}
    (result : identifyJointKernel P.observedGraph query = .identified term) :
    (positive P).identifiable query := by
  intro left right leftPositive _rightPositive observational assignment
  exact ⟨identifyJointKernel_hiddenDAG_identifiableAt query result
    left right observational leftPositive assignment⟩

/-- Literal successful IDC gives native conditional identification on
common support throughout the same positive class.  Full partial-result
soundness is stronger than the common-support equality required here. -/
theorem identifyConditionalKernel_identified (query : ConditionalKernelQuery S)
    {term : ProbabilityTerm S}
    (result : identifyConditionalKernel P.observedGraph query = .identified term) :
    (positive P).conditionalIdentifiable query := by
  intro left right leftPositive _rightPositive observational assignment _leftSupport _rightSupport
  exact ⟨identifyConditionalKernel_hiddenDAG_identifiableAt query result
    left right observational leftPositive assignment⟩

/-- Joint ID succeeds exactly for identifiable queries in the full positive
original-DAG class.  The success witness is its actual computed formula;
failure is contradicted by an actual positive native countermodel pair. -/
theorem identifyJointKernel_identifiable_iff (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S) :
    (positive P).identifiable query ↔
      ∃ term, identifyJointKernel P.observedGraph query = .identified term := by
  constructor
  · intro identified
    cases result : identifyJointKernel P.observedGraph query with
    | identified term => exact ⟨term, result⟩
    | failed fail =>
        exact False.elim
          (identifyJointKernel_hiddenDAG_failed_not_identifiable rich query result identified)
    | unfinished => exact False.elim (identifyJointKernel_ne_unfinished _ query result)
  · rintro ⟨term, result⟩
    exact identifyJointKernel_identified query result

/-- The corresponding iff theorem for full recursive conditional IDC.
Its failure witness separates values on common support for the unchanged
original query, including all prior conditioner-promotion steps. -/
theorem identifyConditionalKernel_identifiable_iff (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S) :
    (positive P).conditionalIdentifiable query ↔
      ∃ term, identifyConditionalKernel P.observedGraph query = .identified term := by
  constructor
  · intro identified
    cases result : identifyConditionalKernel P.observedGraph query with
    | identified term => exact ⟨term, result⟩
    | failed fail =>
        exact False.elim
          (identifyConditionalKernel_hiddenDAG_failed_not_identifiable rich query result identified)
    | unfinished => exact False.elim (identifyConditionalKernel_ne_unfinished _ query result)
  · rintro ⟨term, result⟩
    exact identifyConditionalKernel_identified query result

/-- Positive full-DAG and positive canonical projected-class joint
identifiability agree.  The forward implication realizes every canonical
pair; the reverse uses actual engine success and native soundness.  This is
a query-identifiability equivalence, not equality of the two model classes. -/
theorem positive_identifiable_iff_projected (rich : ObservedSignature.ValueRich S)
    (query : JointKernelQuery S) :
    (positive P).identifiable query ↔
      (GraphModelClass.positive P.observedGraph).identifiable query := by
  constructor
  · exact positive_identifiable_projected query
  · intro identified
    cases result : identifyJointKernel P.observedGraph query with
    | identified term => exact identifyJointKernel_identified query result
    | failed fail =>
        exact False.elim
          (P.observedGraph.identifyJointKernel_failed_not_identifiable rich query result identified)
    | unfinished => exact False.elim (identifyJointKernel_ne_unfinished _ query result)

/-- Conditional identifiability agrees between those same two full positive
classes, with the original common-support relation on both sides. -/
theorem positive_conditionalIdentifiable_iff_projected (rich : ObservedSignature.ValueRich S)
    (query : ConditionalKernelQuery S) :
    (positive P).conditionalIdentifiable query ↔
      (GraphModelClass.positive P.observedGraph).conditionalIdentifiable query := by
  constructor
  · exact positive_conditionalIdentifiable_projected query
  · intro identified
    cases result : identifyConditionalKernel P.observedGraph query with
    | identified term => exact identifyConditionalKernel_identified query result
    | failed fail =>
        exact False.elim
          (P.observedGraph.identifyConditionalKernel_failed_not_identifiable rich query result identified)
    | unfinished => exact False.elim (identifyConditionalKernel_ne_unfinished _ query result)

end HiddenDAGModelClass
end Causality
end Thesis
