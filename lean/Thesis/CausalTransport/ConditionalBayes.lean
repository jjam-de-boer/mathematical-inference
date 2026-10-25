import Thesis.CausalTransport.DSeparation
import Thesis.Causality.IdentificationSearch

namespace Thesis
namespace Causality

open Probability

/-!
# Conditional Bayes derivations with actual source support

The original conditional query decomposes into its joint numerator and
denominator kernels. These syntax equalities and inspectable derivations retain
the same action, outcome and conditioner sets; arbitrary joint derivations can
then be composed into the displayed quotient.

The support constructor is local to the requested reference assignment. It
uses positivity of the original causal conditioner, obtained from the supplied
source-support witness, rather than asking for all interventional denominator
cells to be positive. It does not assume do-calculus soundness to establish
that positivity and does not turn an undefined target into a defined answer.

Current completeness assembly imports this source-local support bridge
directly, independently of any obsolete identification recursion.
-/

/-- Bayes writes `P(Y | do(X), Z)` as `P(Y, Z | do(X)) / P(Z | do(X))`. -/
theorem ConditionalKernelQuery.jointNumerator_sourceTerm
    (q : ConditionalKernelQuery S) :
    q.jointNumerator.sourceTerm =
      .kernel ⟨NodeSet.union q.outcome q.condition, q.action,
        NodeSet.empty⟩ := by
  simp [ConditionalKernelQuery.jointNumerator, JointKernelQuery.sourceTerm]

theorem ConditionalKernelQuery.jointDenominator_sourceTerm
    (q : ConditionalKernelQuery S) :
    q.jointDenominator.sourceTerm =
      .kernel ⟨q.condition, q.action, NodeSet.empty⟩ := by
  simp [ConditionalKernelQuery.jointDenominator, JointKernelQuery.sourceTerm]

theorem ConditionalKernelQuery.bayesDivide_eq_conditioningRight
    (q : ConditionalKernelQuery S) :
    ProbabilityTerm.divide q.jointNumerator.sourceTerm
        q.jointDenominator.sourceTerm =
      .divide
        (.kernel ⟨NodeSet.union q.outcome q.condition, q.action,
          NodeSet.empty⟩)
        (.kernel ⟨q.condition, q.action, NodeSet.empty⟩) := by
  simp [ConditionalKernelQuery.jointNumerator,
    ConditionalKernelQuery.jointDenominator, JointKernelQuery.sourceTerm]

/-- Conditioning with empty given-set: `P(Y | do(X), Z) = P(Y, Z | do(X)) / P(Z | do(X))`. -/
def conditionalBayesDerivation {G : ObservedGraph S}
    (q : ConditionalKernelQuery S) :
    PathDoCalculusDerivation G q.sourceTerm
      (.divide q.jointNumerator.sourceTerm q.jointDenominator.sourceTerm) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (ConditionalKernelQuery.sourceTerm_eq_conditioningLeft_empty_w q)
    (ConditionalKernelQuery.bayesDivide_eq_conditioningRight q)
    (DoCalculusDerivation.conditioning
      (G := G) (separation := pathRuleSeparation G)
      q.action q.outcome q.condition NodeSet.empty
      (FourWayDisjoint.of_empty_w q.action q.outcome q.condition
        q.action_outcome_disjoint q.action_condition_disjoint
        q.outcome_condition_disjoint))

/-- Two joint identifications, divided, recover the conditional formula. -/
def ofJointIdentifiedIdDerivation {G : ObservedGraph S}
    (q : ConditionalKernelQuery S)
    {numFormula denFormula : ProbabilityTerm S}
    (num :
      PathDoCalculusDerivation G q.jointNumerator.sourceTerm numFormula)
    (den :
      PathDoCalculusDerivation G q.jointDenominator.sourceTerm denFormula) :
    PathDoCalculusDerivation G q.sourceTerm
      (.divide numFormula denFormula) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (conditionalBayesDerivation q)
    (DoCalculusDerivation.divideCongr
      (G := G) (separation := pathRuleSeparation G) num den)

/-- The Bayes quotient of two unconditional interventional kernels is
defined once the source kernel `P(Y | do(X), Z)` is: the denominator
cylinder is that kernel's conditioner. -/
noncomputable def conditionalBayes_supportedAt
    (model : FiniteLatentSCM S) (q : ConditionalKernelQuery S)
    (assignment : S.Assignment)
    (sourceSupported : q.sourceTerm.SupportedAt model assignment) :
    (ProbabilityTerm.divide q.jointNumerator.sourceTerm
      q.jointDenominator.sourceTerm).SupportedAt model assignment := by
  have hsrc :=
    ConditionalKernelQuery.sourceTerm_eq_operationKernel q
  let srcKernel : Kernel S := q.operationKernel
  have srcSupported' :
      ProbabilityTerm.SupportedAt model (.kernel srcKernel) assignment :=
    ProbabilityTerm.SupportedAt.congr hsrc sourceSupported
  have hdist :
      srcKernel.distribution model assignment =
        (Kernel.mk q.condition q.action NodeSet.empty).distribution
          model assignment :=
    Kernel.distribution_eq_of_action model q.outcome q.condition
      q.action q.condition NodeSet.empty assignment
  have hnum :=
    Kernel.unconditionalDenote model
      (NodeSet.union q.outcome q.condition) q.action assignment
  have hden :=
    Kernel.unconditionalDenote model q.condition q.action assignment
  let numVal :=
    ((Kernel.mk (NodeSet.union q.outcome q.condition) q.action
        NodeSet.empty).distribution model assignment).probVal
      (Kernel.agreesOn (NodeSet.union q.outcome q.condition) assignment)
  let denVal :=
    ((Kernel.mk q.condition q.action NodeSet.empty).distribution
      model assignment).probVal (Kernel.agreesOn q.condition assignment)
  have hpos : 0 < denVal.num := by
    have hsrcPos :=
      Kernel.conditionPositive_of_supportedAt model srcKernel
        assignment srcSupported'
    dsimp [denVal]
    rw [← hdist]
    simpa [srcKernel, Kernel.conditionEvent, ConditionalKernelQuery.operationKernel]
      using hsrcPos
  have hdiv :
      ProbabilityResult.Equivalent
        ((ProbabilityTerm.divide q.jointNumerator.sourceTerm
          q.jointDenominator.sourceTerm).denote model assignment)
        (ProbabilityResult.divide (some numVal) (some denVal)) := by
    simpa [ProbabilityTerm.denote,
      ConditionalKernelQuery.jointNumerator,
      ConditionalKernelQuery.jointDenominator, JointKernelQuery.sourceTerm,
      JointKernelQuery.operationKernel] using
      ProbabilityResult.divide_congr hnum hden
  have hdefinedEq :
      ProbabilityResult.divide (some numVal) (some denVal) =
        some (QProb.div numVal denVal hpos) := by
    simp only [ProbabilityResult.divide]
    rw [dif_pos hpos]
  have hdefined :
      ProbabilityResult.Equivalent
        (ProbabilityResult.divide (some numVal) (some denVal))
        (some (QProb.div numVal denVal hpos)) := by
    rw [hdefinedEq]
    exact ProbabilityResult.Equivalent.value (QProb.equiv_refl _)
  exact ⟨QProb.div numVal denVal hpos,
    ProbabilityResult.trans hdiv hdefined⟩

end Causality
end Thesis
