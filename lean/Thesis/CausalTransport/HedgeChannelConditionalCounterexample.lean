import Thesis.CausalTransport.HedgeChannelCounterexample
import Thesis.CausalTransport.HedgeChannelMarginal
import Thesis.CausalTransport.HedgeChannelConditionalGap
import Thesis.Causality.ValueRefinementMarginal
import Thesis.CausalTransport.ConditionalFailureExtraction

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Conditional channel countermodels with a matched binary denominator

The unrestricted channel construction already supplies a positive
original-query numerator counterexample for every supplied hedge.  A
conditional counterexample needs more: its conditioning kernel must agree in
the same final original-label models.  `ValueRefinementMarginal` now proves
the full-label transport of that agreement, so the remaining semantic premise
can be stated directly on the actual installed Boolean pair.

The constructor below does not assume denominator identifiability, full-joint
interventional equality, protected refinement pivots, or a seed-only action.
It compares exactly the conditioning events under cuts on the unchanged
original action set.  The matched marginal is transported through encoding
and private label refinement and then combined with the checked chain-rule
argument.  The recursive-failure adapter retains that very pair along its
already extracted observation/action exchange trace.

`HedgeChannelMarginal` discharges the binary marginal premise from a supplied
finite outcome-flow balance direction.  In particular, an omitted small-flow
sink supplies the direction automatically, with no old carrier route test.
The general binary-marginal adapter remains reusable when another argument
proves equality.  Existence of a suitable balance direction is not asserted
for every irreducible terminal, so these constructors do not yet inhabit the
universal conditional field of `PublishedCompleteness`.

The normalized-cell route is independent of that matched-marginal family.
Its channel constructor now lifts an actual unequal-denominator source cell
to all original labels, and the last failure adapter below restores that
same final pair along the complete exchange trace.  Constructing separating
typed signals at every arbitrary terminal remains the general semantic leaf.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}

/-- Assemble an original conditional counterexample from the unrestricted
numerator hedge and equality of all actual Boolean conditioning events under
the full original action.  The denominator is proved for the same two refined
models whose original numerator kernel is separated. -/
noncomputable def conditionalCounterexampleOfBinaryMarginals
    (query : ConditionalKernelQuery S) (w : HedgeWitness G query.jointNumerator)
    (rich : ObservedSignature.ValueRich S)
    (equivalent : forall (target : Fin S.count -> Option Bool),
      (forall child, (target child).isSome = query.action child) ->
      forall event : Event S.binary.Assignment, EventDependsOnlyOn (S := S.binary) query.condition event ->
        QProb.Equiv
          ((leftModel w rich (outcomeFlowSignal w) (outcomeFlowSignal w)).interventionalValue target event)
          ((rightModel w (outcomeFlowSignal w) (outcomeFlowSignal w)).interventionalValue target event)) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query := by
  let joint := counterexample w rich
  have denominator : query.jointDenominator.ValueEquivalent joint.left joint.right := by
    change query.jointDenominator.ValueEquivalent
      (ObservedValueRefinement.refine rich (BinaryEncoding.model rich
        (leftModel w rich (outcomeFlowSignal w) (outcomeFlowSignal w))))
      (ObservedValueRefinement.refine rich (BinaryEncoding.model rich
        (rightModel w (outcomeFlowSignal w) (outcomeFlowSignal w))))
    exact query.jointDenominator.refine_encoded_valueEquivalent_of_binaryMarginals rich _ _ equivalent
  exact ConditionalCounterexampleIn.ofJointNumeratorOfDenominatorEquivalent
    (C := GraphModelClass.positive G) (fun member => member.2) query joint denominator

/-- A supplied finite balance direction proves the actual conditioning
marginal comparison internally.  The same channel pair is then encoded and
refined on the unchanged alphabet, and its original joint numerator gap
separates the original conditional kernel.  No semantic equality premise is
left for the caller of this constructor. -/
noncomputable def conditionalCounterexampleOfBalanceDirection
    (query : ConditionalKernelQuery S) (w : HedgeWitness G query.jointNumerator)
    (rich : ObservedSignature.ValueRich S) (direction : OutcomeFlowBalanceDirection w query.condition) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  conditionalCounterexampleOfBinaryMarginals query w rich
    (direction.models_interventionalMarginals_equivalent rich)

/-- An original conditional query whose conditioner omits a small-flow
sink has a positive full-alphabet channel counterexample.  The sink may have
other declared graph children: only its selected outcome-flow successor must
be absent.  Older carrier route-permission and protected-coordinate tests,
shared-switch assumptions, and guessed denominator equalities are not used. -/
noncomputable def conditionalCounterexampleOfSmallFlowSink
    (query : ConditionalKernelQuery S) (w : HedgeWitness G query.jointNumerator)
    (rich : ObservedSignature.ValueRich S) (balance : Fin S.count)
    (inside : w.small balance = true) (unused : w.smallOutcomeFlowSuccessor balance = none)
    (omitted : query.condition balance = false) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  conditionalCounterexampleOfBalanceDirection query w rich
    (OutcomeFlowBalanceDirection.ofSmallSink w query.condition balance inside unused omitted)

end HedgeChannelInstallation

open Probability HedgeChannelInstallation

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}

/-- Close an arbitrary-depth IDC failure once its actual irreducible
terminal pair has a matched Boolean conditioning marginal.  The general
numerator pair and full-alphabet denominator transport are internal; the
certified exchange trace restores the original conditional query. -/
noncomputable def ConditionalKernelFailure.counterexampleOfChannelBinaryMarginals
    {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure G query fail) (rich : ObservedSignature.ValueRich S)
    (equivalent : forall (target : Fin S.count -> Option Bool),
      (forall child, (target child).isSome = failure.terminal.action child) ->
      forall event : Event S.binary.Assignment,
        EventDependsOnlyOn (S := S.binary) failure.terminal.condition event ->
        QProb.Equiv
          ((leftModel failure.hedge.witness rich (outcomeFlowSignal failure.hedge.witness)
            (outcomeFlowSignal failure.hedge.witness)).interventionalValue target event)
          ((rightModel failure.hedge.witness (outcomeFlowSignal failure.hedge.witness)
            (outcomeFlowSignal failure.hedge.witness)).interventionalValue target event)) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  failure.counterexampleOfTerminal (C := GraphModelClass.positive G) (fun member => member.2)
    (conditionalCounterexampleOfBinaryMarginals failure.terminal failure.hedge.witness rich equivalent)

/-- A balanced terminal direction closes a complete arbitrary-depth IDC
failure with the same two final models.  The terminal marginal theorem and
full-alphabet transport are internal; the checked exchange trace restores
the original conditional query without any selected auxiliary countermodel. -/
noncomputable def ConditionalKernelFailure.counterexampleOfChannelBalanceDirection
    {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure G query fail) (rich : ObservedSignature.ValueRich S)
    (direction : OutcomeFlowBalanceDirection failure.hedge.witness failure.terminal.condition) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  failure.counterexampleOfTerminal (C := GraphModelClass.positive G) (fun member => member.2)
    (conditionalCounterexampleOfBalanceDirection failure.terminal failure.hedge.witness rich direction)

/-- Close an arbitrary-depth IDC failure from a nonzero complete normalized
cell change at its actual terminal.  Original-alphabet positivity and the
unequal-denominator cell lift are internal; the certified exchange trace
restores the original conditional on the same two final models.  The caller
supplies typed terminal signals and a finite arithmetic gap, not a countermodel
or an assumed semantic conditioning-marginal equality. -/
noncomputable def ConditionalKernelFailure.counterexampleOfChannelNormalizedCellChange
    {query : ConditionalKernelQuery S} {fail : IdentificationFail S}
    (failure : ConditionalKernelFailure G query fail) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (reference : S.binary.Assignment)
    (nonzero : normalizedCellChange failure.hedge.witness rich smallSignal backgroundSignal reference ≠ 0) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  failure.counterexampleOfTerminal (C := GraphModelClass.positive G) (fun member => member.2)
    (conditionalCounterexampleOfNormalizedCellChange failure.hedge.witness rich smallSignal backgroundSignal
      reference nonzero)

end Causality
end Thesis
