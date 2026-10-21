import Thesis.CausalTransport.ConditionalFailureCore
import Thesis.CausalTransport.HedgePositive

namespace Thesis
namespace Causality

/-!
# A qualified carrier case for conditional counterexamples

This positive-model constructor applies when the common roots are queried
outcomes and the conditioner is outside the large hedge forest. The supplied
carrier pair then agrees on the denominator and separates the numerator.
These geometric premises are sufficient, not requirements of the general
conditional-failure theorem.

The unchanged constructor is separated from `ConditionalFailureCore` so the
general exchange trace and terminal assembly do not import carrier-model
machinery. `ConditionalFailureExtraction` remains the compatibility import
for both this local case and the general core.
-/

/-- A positive conditional countermodel whenever every common root is a
queried outcome and the conditioner lies outside the hedge's large forest.

The root carrier pair separates the numerator by finite marginalization.
Its conditioner coordinates agree pointwise under the intervention because
both constructed mechanisms read the same private backgrounds outside the
large forest.  The matched-denominator chain lemma therefore separates the
conditional in that very pair.  No denominator-identifiability assumption
is made: graphical descendants in the conditioner are allowed, provided
they are outside this forest.  Nor does the construction need a successful
exchange test; it can close an irreducible nonempty-condition terminal.

These explicit geometric hypotheses do not hold for every hedge, so the
general irreducible conditional countermodel leaf remains separate.  The
companion `HedgeConditionalMarginal` supplies a stronger constructor retaining
only the roots-in-outcome hypothesis; this local pointwise adapter is kept
without creating an import cycle back to its marginal proof. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootsSubsetOutcomeOfConditionOutsideLarge
    {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (rootsInOutcome : NodeSet.Subset w.roots query.outcome)
    (conditionOutside : NodeSet.Disjoint query.condition w.large) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  let joint := w.positiveCounterexampleOfRootsSubsetOutcome rich
    (rootsInOutcome.trans (NodeSet.subset_union_left query.outcome query.condition))
  ConditionalCounterexampleIn.ofJointNumeratorOfDenominatorEquivalent
    (C := GraphModelClass.positive graph) (fun member => member.2) query joint
    (w.carrierDefectParityModels_valueEquivalent_outsideLarge rich
      query.jointDenominator conditionOutside)

end Causality
end Thesis
