import Thesis.CausalTransport.Soundness

namespace Thesis
namespace Causality

open Probability

/-!
# A query-local observational support boundary for rule-2 identification

The probability and SCM layers permit zeros.  For a single action/observation
exchange, the needed observational regularity is only positivity of the
displayed action cylinder at the reference assignment.  Neither the outcome
cell nor every complete observed assignment has to carry positive mass.

This module proves that support boundary directly, then applies the inhabited
published soundness package to a concrete rule-2 leaf.  Finally it compares
the resulting effect in two observationally equal compatible models.  The
local overlap condition transfers automatically between those models because
it is observable; it is not a condition on an unknown causal probability.

This is a sufficient local identification result for queries satisfying the
stated graph test.  It is not the general recursive ID/IDC compiler, does not
claim that the action-cylinder condition is necessary for every identifiable
query, and does not yet cover full hidden-DAG SCMs outside the compatible
latent-root model class.  No external soundness assumption is supplied.
-/

/-- Positive observational mass of exactly one selected cylinder.  This is
assignment-local and is decidable from the finite observational record; it
does not require a positive outcome or a positive full joint distribution. -/
def ObservationalCylinderPositiveAt (model : FiniteLatentSCM S)
    (nodes : NodeSet S) (reference : S.Assignment) : Prop :=
  0 < (model.observationalDist.probVal (Kernel.agreesOn nodes reference)).num

/-- Observational agreement preserves the local support condition.  The
finite rational numerator test is invariant under probability equivalence. -/
theorem ObservationalCylinderPositiveAt.transfer
    {left right : FiniteLatentSCM S}
    (observational : ProbabilityTerm.ObservationalAgreement left right)
    {nodes : NodeSet S} {reference : S.Assignment}
    (positive : ObservationalCylinderPositiveAt left nodes reference) :
    ObservationalCylinderPositiveAt right nodes reference :=
  (QProb.equiv_num_pos_iff
    (observational (Kernel.agreesOn nodes reference))).mp positive

/-- Construct the displayed conditional from its actual finite numerator and
positive conditioner.  Zero outcome mass is allowed, and no representative
is chosen from an existence proposition. -/
noncomputable def observationalConditional_supportedAt_of_positive
    (model : FiniteLatentSCM S) (outcome condition : NodeSet S)
    (reference : S.Assignment)
    (positive : ObservationalCylinderPositiveAt model condition reference) :
    (ProbabilityTerm.kernel ⟨outcome, NodeSet.empty, condition⟩).SupportedAt
      model reference := by
  let kernel : Kernel S := ⟨outcome, NodeSet.empty, condition⟩
  have noAction : kernel.hasAction = false :=
    ProbabilityTerm.actionFree_hasAction_false kernel (fun _ => rfl)
  have observational : kernel.distribution model reference = model.observationalDist := by
    simp only [Kernel.distribution, noAction, Bool.false_eq_true, if_false]
  let numerator := (kernel.distribution model reference).probVal
    (kernel.numeratorEvent reference)
  let denominator := (kernel.distribution model reference).probVal
    (kernel.conditionEvent reference)
  have denominatorPositive : 0 < denominator.num := by
    simpa only [denominator, observational, kernel, Kernel.conditionEvent] using positive
  refine ⟨QProb.div numerator denominator denominatorPositive, ?_⟩
  change ProbabilityResult.Equivalent
    (ProbabilityResult.divide (some numerator) (some denominator))
    (some (QProb.div numerator denominator denominatorPositive))
  simp only [ProbabilityResult.divide, dif_pos denominatorPositive]
  exact .value (QProb.equiv_refl _)

namespace JointKernelQuery

/-- The observational conditional supplied by the direct rule-2 exchange.
It remains partial outside its actual observational conditioning support. -/
def observationalActionConditional (query : JointKernelQuery S) : ProbabilityTerm S :=
  .kernel ⟨query.outcome, NodeSet.empty, query.action⟩

/-- A rule-2 action/observation exchange identifies the displayed effect
at locally supported action values, even in a distribution containing zeros.
The graph condition is the incoming-empty, outgoing-action cut. -/
noncomputable def unconfounded_soundAt (G : ObservedGraph S)
    (query : JointKernelQuery S)
    (separated : G.dSeparated
      (.barUnderline NodeSet.empty query.action)
      query.outcome query.action NodeSet.empty = true)
    (model : ExactModel S) (compatible : Compatible model G)
    (reference : S.Assignment)
    (overlap : ObservationalCylinderPositiveAt model query.action reference) :
    ProbabilityTerm.EquivalentAt model query.sourceTerm
      query.observationalActionConditional reference := by
  let application : DoRuleApplication G
      (rule2Left NodeSet.empty query.outcome query.action NodeSet.empty)
      (rule2Right NodeSet.empty query.outcome query.action NodeSet.empty) :=
    .rule2 NodeSet.empty query.outcome query.action NodeSet.empty
      (FourWayDisjoint.emptyAction query.outcome query.action NodeSet.empty
        query.action_outcome_disjoint.symm (NodeSet.disjoint_empty_right _)
        (NodeSet.disjoint_empty_right _))
      (by simpa only [NodeSet.union_empty_left] using separated)
  let sourceSupported : query.sourceTerm.SupportedAt model reference :=
    ⟨((Kernel.mk query.outcome query.action NodeSet.empty).distribution
        model reference).probVal (Kernel.agreesOn query.outcome reference),
      Kernel.unconditionalDenote model query.outcome query.action reference⟩
  let targetSupported := observationalConditional_supportedAt_of_positive
    model query.outcome query.action reference overlap
  have applied := (G.publishedSoundness.primitive model compatible).doRule
    reference application
    (by simpa only [rule2Left, NodeSet.union_empty_left, sourceTerm]
      using sourceSupported)
    (by simpa only [rule2Right, NodeSet.union_empty_right]
      using targetSupported)
  simpa only [sourceTerm, observationalActionConditional, rule2Left, rule2Right,
    NodeSet.union_empty_left, NodeSet.union_empty_right] using applied

/-- Observationally equal compatible models have the same effect at the
reference whenever the observable local action cylinder is supported.
Only the left model's overlap premise is requested: observational agreement
constructively supplies the right model's same positive support. -/
noncomputable def unconfounded_identifiableAt (G : ObservedGraph S)
    (query : JointKernelQuery S)
    (separated : G.dSeparated
      (.barUnderline NodeSet.empty query.action)
      query.outcome query.action NodeSet.empty = true)
    (left right : ExactModel S) (leftCompatible : Compatible left G)
    (rightCompatible : Compatible right G)
    (observational : ObservationallyEquivalent left right)
    (reference : S.Assignment)
    (overlap : ObservationalCylinderPositiveAt left query.action reference) :
    ProbabilityResult.Equivalent (query.sourceTerm.denote left reference)
      (query.sourceTerm.denote right reference) :=
  ProbabilityResult.trans
    (unconfounded_soundAt G query separated left leftCompatible reference overlap)
    (ProbabilityResult.trans
      (ProbabilityTerm.actionFree_invariant left right observational
        query.observationalActionConditional (fun _ => rfl) reference)
      (ProbabilityResult.symm
        (unconfounded_soundAt G query separated right rightCompatible reference
          (ObservationalCylinderPositiveAt.transfer observational overlap))))

end JointKernelQuery
end Causality
end Thesis
