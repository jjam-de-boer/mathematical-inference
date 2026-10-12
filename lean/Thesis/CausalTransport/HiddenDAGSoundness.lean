import Thesis.CausalTransport.HiddenDAGSemantics
import Thesis.CausalTransport.Soundness

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {P : FiniteLatentProjection S}

/-!
# Support-qualified do-calculus soundness for all finite hidden DAGs

The full hidden model is first collapsed with proved intervention preservation.
Its root model need not be canonical semi-Markovian: the actual path partition
theorems require only the projected graph.  We use that weaker, already proved
boundary directly, not `Compatible` or a fictitious two-child proof.

Native kernel and term preservation then reads the resulting soundness back
in the original full-DAG probability records.  Every do-rule and every
probability-algebra constructor is covered at its explicit recursive local
support.  Zeros are allowed; unsupported positive-mass branches and null
conditioners are not assigned arbitrary values.

No `PublishedLatentProjection`, published soundness assumption, global
positivity premise, or extra hidden-DAG law is supplied by the caller.  This
establishes soundness.  The reverse positive countermodel construction and
published completeness are supplied separately by `HiddenDAGCompleteness`;
`GuardedKernelSuccessCompilation` now supplies the recursive guarded joint
compiler from local data, and `GuardedKernelSoundness` interprets that compiler
natively. `GuardedConditionalSuccessCompilation` and
`GuardedConditionalSoundness` now supply the corresponding local-data
promotion/Bayes compiler and native interpretation for conditional IDC.
An unrestricted zero-class completeness equivalence is not asserted here.
-/

namespace FiniteHiddenDAGSCM

/-- Apply the proved path partition argument to the actual collapsed root
model.  Projected-graph equality is the only model-compatibility input; roots
may retain three or more children. -/
noncomputable def collapsedPathPrimitiveSoundness (M : FiniteHiddenDAGSCM S P) :
    PathPrimitiveSoundness P.observedGraph M.toLatentRootSCM := by
  let witnesses := PathDoRulePartitionWitnesses.ofPathProjected
    P.observedGraph M.toLatentRootSCM
    (fun first second => M.toLatentRootSCM_projectedGraph first second)
  exact PathPrimitiveSoundness.ofDoRule M.toLatentRootSCM P.observedGraph
    witnesses.toProductCrossProductLaws.toDistributionLaws.toCrossProductSoundness.toDoRule

/-- Each of the three path do-rules is sound in the original full hidden
model whenever its displayed native endpoint kernels are supported. -/
noncomputable def pathDoRule_soundAt (M : FiniteHiddenDAGSCM S P)
    {left right : Kernel S} (assignment : S.Assignment)
    (application : PathDoRuleApplication P.observedGraph left right)
    (leftSupported : M.TermSupportedAt (.kernel left) assignment)
    (rightSupported : M.TermSupportedAt (.kernel right) assignment) :
    M.TermEquivalentAt (.kernel left) (.kernel right) assignment :=
  M.termEquivalentAt_of_collapsed _ _ assignment
    (M.collapsedPathPrimitiveSoundness.doRule assignment application
      (M.termSupportedAt_to_collapsed _ _ leftSupported)
      (M.termSupportedAt_to_collapsed _ _ rightSupported))

/-- The executable graph tests imply the same native do-rule soundness.
Their checked path translation is used, not an externally assumed criterion. -/
noncomputable def doRule_soundAt (M : FiniteHiddenDAGSCM S P)
    {left right : Kernel S} (assignment : S.Assignment)
    (application : DoRuleApplication P.observedGraph left right)
    (leftSupported : M.TermSupportedAt (.kernel left) assignment)
    (rightSupported : M.TermSupportedAt (.kernel right) assignment) :
    M.TermEquivalentAt (.kernel left) (.kernel right) assignment :=
  M.pathDoRule_soundAt assignment application.toPathChecked leftSupported rightSupported

end FiniteHiddenDAGSCM

/-- Soundness for the entire derivation language in native full-hidden-DAG
semantics.  Its support argument contains every required endpoint and subtree,
including finite marginal substitutions and positive-only guarded factors.
No separate semantic theorem is accepted as a premise. -/
noncomputable def DoCalculusDerivation.hiddenDAG_denotational_soundAt
    {model : FiniteHiddenDAGSCM S P} {assignment : S.Assignment}
    {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation P.observedGraph left right)
    (supported : HiddenDAGLocalDerivationSupport model assignment derivation) :
    model.TermEquivalentAt left right assignment :=
  model.termEquivalentAt_of_collapsed left right assignment
    (derivation.denotational_soundAt model.collapsedPathPrimitiveSoundness.compileChecked
      supported.toCollapsed)

/-- Compile a published path derivation with the inhabited graph criterion
and interpret it in the original hidden model.  The caller supplies its
native local support tree, not a latent-projection interface. -/
noncomputable def PathDoCalculusDerivation.hiddenDAG_denotational_soundAt
    {model : FiniteHiddenDAGSCM S P} {assignment : S.Assignment}
    {left right : ProbabilityTerm S}
    (derivation : PathDoCalculusDerivation P.observedGraph left right)
    (supported : HiddenDAGLocalDerivationSupport model assignment
      (derivation.compile P.observedGraph.dSeparationCorrectness)) :
    model.TermEquivalentAt left right assignment :=
  (derivation.compile P.observedGraph.dSeparationCorrectness).hiddenDAG_denotational_soundAt supported

/-- An action-free derivation identifies the source value between two
observationally equal full hidden models at the supplied local support.
This is the semantic identification consequence of the actual derivation;
it does not claim that every identifiable query already has such a compiler. -/
noncomputable def DoCalculusDerivation.hiddenDAG_identifiableAt
    (leftModel rightModel : FiniteHiddenDAGSCM S P)
    (observational : leftModel.ObservationalAgreement rightModel)
    {source formula : ProbabilityTerm S}
    (derivation : DoCalculusDerivation P.observedGraph source formula)
    (actionFree : formula.ActionFree) (assignment : S.Assignment)
    (leftSupported : HiddenDAGLocalDerivationSupport leftModel assignment derivation)
    (rightSupported : HiddenDAGLocalDerivationSupport rightModel assignment derivation) :
    ProbabilityResult.Equivalent
      (leftModel.termDenote source assignment) (rightModel.termDenote source assignment) :=
  ProbabilityResult.trans (derivation.hiddenDAG_denotational_soundAt leftSupported)
    (ProbabilityResult.trans
      (FiniteHiddenDAGSCM.actionFree_invariant leftModel rightModel observational formula actionFree assignment)
      (ProbabilityResult.symm (derivation.hiddenDAG_denotational_soundAt rightSupported)))

namespace JointKernelQuery

/-- A concrete rule-2 identification leaf on *all* finite hidden DAGs.
Its only regularity condition is positive observable action-cylinder mass
at this assignment.  Outcomes may be zero, and the rest of the observational
law need not be positive.  Multi-child collapsed roots are allowed. -/
noncomputable def hiddenDAG_unconfounded_soundAt
    (query : JointKernelQuery S)
    (separated : P.observedGraph.dSeparated
      (.barUnderline NodeSet.empty query.action)
      query.outcome query.action NodeSet.empty = true)
    (model : FiniteHiddenDAGSCM S P) (assignment : S.Assignment)
    (overlap : model.ObservationalCylinderPositiveAt query.action assignment) :
    model.TermEquivalentAt query.sourceTerm
      (.kernel ⟨query.outcome, NodeSet.empty, query.action⟩) assignment := by
  let application : DoRuleApplication P.observedGraph
      (rule2Left NodeSet.empty query.outcome query.action NodeSet.empty)
      (rule2Right NodeSet.empty query.outcome query.action NodeSet.empty) :=
    .rule2 NodeSet.empty query.outcome query.action NodeSet.empty
      (FourWayDisjoint.emptyAction query.outcome query.action NodeSet.empty
        query.action_outcome_disjoint.symm (NodeSet.disjoint_empty_right _)
        (NodeSet.disjoint_empty_right _))
      (by simpa only [NodeSet.union_empty_left] using separated)
  let sourceSupported := model.kernelSupportedAt_unconditional query.outcome query.action assignment
  let targetSupported := model.kernelSupportedAt_of_observational_overlap
    ⟨query.outcome, NodeSet.empty, query.action⟩ assignment
    (by simpa only [NodeSet.union_empty_left] using overlap)
  have applied := model.doRule_soundAt assignment application
    (by simpa only [rule2Left, NodeSet.union_empty_left, sourceTerm] using sourceSupported)
    (by simpa only [rule2Right, NodeSet.union_empty_right] using targetSupported)
  simpa only [sourceTerm, rule2Left, rule2Right,
    NodeSet.union_empty_left, NodeSet.union_empty_right] using applied

/-- Only one observationally equal model must supply the overlap premise.
Native observational agreement transfers it to the other model, then the
two actual rule-2 reductions identify the effect on that supported action cell. -/
noncomputable def hiddenDAG_unconfounded_identifiableAt
    (query : JointKernelQuery S)
    (separated : P.observedGraph.dSeparated
      (.barUnderline NodeSet.empty query.action)
      query.outcome query.action NodeSet.empty = true)
    (left right : FiniteHiddenDAGSCM S P)
    (observational : left.ObservationalAgreement right)
    (assignment : S.Assignment)
    (overlap : left.ObservationalCylinderPositiveAt query.action assignment) :
    ProbabilityResult.Equivalent
      (left.termDenote query.sourceTerm assignment) (right.termDenote query.sourceTerm assignment) :=
  ProbabilityResult.trans
    (query.hiddenDAG_unconfounded_soundAt separated left assignment overlap)
    (ProbabilityResult.trans
      (FiniteHiddenDAGSCM.actionFree_invariant left right observational
        (.kernel ⟨query.outcome, NodeSet.empty, query.action⟩) (fun _ => rfl) assignment)
      (ProbabilityResult.symm (query.hiddenDAG_unconfounded_soundAt separated right assignment
        (FiniteHiddenDAGSCM.ObservationalCylinderPositiveAt.transfer observational overlap))))

end JointKernelQuery
end Causality
end Thesis
