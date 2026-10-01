import Thesis.CausalTransport.HedgeInterventionalMarginal
import Thesis.CausalTransport.ConditionalFailureExtraction

namespace Thesis
namespace Causality

/-!
# Conditional hedge countermodels with arbitrary conditioners

The earlier outside-forest construction obtained matching denominators by
pointwise agreement of private-background mechanisms.  That sufficient
condition excludes conditioners inside either forest, even when their
marginals in the very same countermodel pair agree.

`HedgeInterventionalMarginal` now proves the required equality directly:
omitting one common root gives identical marginal laws in the two actual
carrier SCMs, under any intervention and on the full observed alphabets.
When all common roots occur in the numerator and at least one is a queried
outcome, outcome/condition disjointness supplies such an omitted root.  Other
common roots may be conditioners.  The existing numerator gap and matched-
denominator chain argument therefore construct the original conditional
countermodel without an outside-forest condition.  A Boolean meeting test
recovers a queried root constructively; the all-roots-in-outcome specialization
uses the hedge's already supplied common root instead.

This is a semantic countermodel constructor, not an assertion of general
completeness.  It retains explicit root coverage and outcome-contact
hypotheses.  Arbitrary original-query root routing and the other irreducible
conditional terminals remain separate obligations of the published
completeness assembler.
-/

/-- A conditional countermodel when all common roots occur in the numerator
and one supplied common root is a queried outcome.

Only that one root must be absent from the conditioner.  Every other root may
belong to the queried outcome or to the conditioner: the full numerator still
detects their separating parity, while the root-omitted marginal theorem
matches the conditioning denominator.  This is strictly more general than
requiring every common root to be a queried outcome.

The balance vertex is supplied as finite data with membership proofs; no
choice of a witness from propositional existence is performed. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootsSubsetNumeratorOfRootInOutcome
    {S : ObservedSignature.{0}} {graph : ObservedGraph S}
    {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator)
    (rich : ObservedSignature.ValueRich S)
    (rootsInNumerator : NodeSet.Subset w.roots query.jointNumerator.outcome)
    (balance : Fin S.count) (root : w.roots balance = true)
    (inOutcome : query.outcome balance = true) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  let joint := w.positiveCounterexampleOfRootsSubsetOutcome rich rootsInNumerator
  let omitted := query.outcome_condition_disjoint balance inOutcome
  ConditionalCounterexampleIn.ofJointNumeratorOfDenominatorEquivalent
    (C := GraphModelClass.positive graph) (fun member => member.2) query joint
    (w.carrierDefectParityModels_valueEquivalent_of_rootOmitted rich
      balance root query.jointDenominator omitted)

/-- The same general constructor with its queried root recovered from a
finite Boolean meeting test.  The search uses the existing enumerated node
set, not a propositional choice principle.  All roots must be covered by the
numerator, but only one must meet the queried outcome. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootsSubsetNumeratorOfRootsMeetOutcome
    {S : ObservedSignature.{0}} {graph : ObservedGraph S}
    {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator)
    (rich : ObservedSignature.ValueRich S)
    (rootsInNumerator : NodeSet.Subset w.roots query.jointNumerator.outcome)
    (meetsOutcome : NodeSet.meetsBool w.roots query.outcome = true) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  w.positiveConditionalCounterexampleOfRootsSubsetNumeratorOfRootInOutcome rich rootsInNumerator
    (NodeSet.getMeeting w.roots query.outcome meetsOutcome)
    (NodeSet.getMeeting_left meetsOutcome) (NodeSet.getMeeting_right meetsOutcome)

/-- A positive countermodel for a conditional whose outcomes contain every
common root of the supplied numerator hedge.

The conditioner can lie inside the large forest, inside the small forest,
or outside both.  Disjointness from the queried outcomes ensures only that
it omits the hedge's supplied common root.  The marginal theorem then matches
the denominator in the same two models that separate the numerator; it does
not assume that the denominator is identifiable throughout the model class.

No successful IDC exchange, irreducibility test, or fresh model selection is
needed.  Positivity, observational equality, and numerator separation are
inherited from the constructive full-alphabet carrier pair. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootsSubsetOutcome
    {S : ObservedSignature.{0}} {graph : ObservedGraph S}
    {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator)
    (rich : ObservedSignature.ValueRich S)
    (rootsInOutcome : NodeSet.Subset w.roots query.outcome) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  w.positiveConditionalCounterexampleOfRootsSubsetNumeratorOfRootInOutcome rich
    (rootsInOutcome.trans (NodeSet.subset_union_left query.outcome query.condition))
    w.actionRoot w.actionRoot_in_roots
    (rootsInOutcome w.actionRoot w.actionRoot_in_roots)

end Causality
end Thesis
