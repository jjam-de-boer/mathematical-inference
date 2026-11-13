import Thesis.CausalTransport.HedgeChannelInterventional
import Thesis.CausalTransport.HedgeChannelObservational
import Thesis.CausalTransport.HedgeChannelConditionalCell
import Thesis.CausalTransport.ValueRefinementConditionalCounterexample
import Thesis.Probability.FiniteRatioPerturbation

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Conditional channel gaps without a matched conditioning marginal

The outcome-flow balance construction proves equality of the conditioning
marginal for a particular pair.  Such a direction need not exist when the
conditioner inspects the entire flow boundary.  This module takes a different
route: retain both actual likelihood changes and cross-multiply the two
normalized conditional cells.  A nonzero normalized change separates the
conditional even when its conditioning marginal also changes.

Every change below is the complete permitted full-small sum, integrated on
the actual original-action cut and projected to the exact event.  It is not
an assumed likelihood polynomial or a selected monomial.  The unchanged
natural left masses multiply those two signed sums.  The existing complete
intervention expansion proves the resulting cross-product criterion.

The signals are arbitrary typed small and background parent signals.  Thus
an alternative collider or active-path signal can use this normalization
argument instead of forcing the default outcome-flow pair to have equal
denominators.  Compatibility, positivity, observational equality and the
separated conditional all concern that very pair.

The Boolean constructor exposes the source pair.  The full-alphabet
constructor retains its supplied separated cell through explicit coordinate
recoding, encoding and private label refinement.  It does not repeat a search
over the installed response-function models.  Choosing signals which give
a nonzero cell is still required for each use of this constructor.  This
particular family does not cover every irreducible terminal: the shared-latent
boundary regression proves agreement at every cell for every typed parent
signal on a genuine non-identifiable query.  The full conditional argument
therefore also needs actual latent-path readouts or a more general pair, not
an assertion that parent-signal tuning always succeeds.  The general Boolean
countermodel alphabet lift remains applicable to those alternative pairs.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}
  {query : ConditionalKernelQuery S}

/-- Interpret the unchanged original action, outcome and condition sets
on the Boolean signature.  No node is added, removed or promoted. -/
abbrev binaryConditionalQuery (query : ConditionalKernelQuery S) : ConditionalKernelQuery S.binary :=
  query.binary

/-- Project the entire surviving full-small likelihood difference onto
one supplied event.  Both complete finite sums and conflicting zero cells
are retained, including all permitted background interactions. -/
def projectedEventChange (w : HedgeWitness G query.jointNumerator)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (event : Event S.binary.Assignment) : Int :=
  ((S.binary.assignmentEnumeration.filter event).map (fun sample =>
    ((rightFullChoicesUnder w target).map
      (rightTermIntegralUnder w smallSignal backgroundSignal target sample)).sum)).sum

/-- The two actual projected changes, not independently assumed changes
of abstract masses.  Forcing the stored action seed is the only condition
needed by the existing complete intervention-side expansion. -/
theorem eventNumerator_change (w : HedgeWitness G query.jointNumerator)
    (rich : ObservedSignature.ValueRich S) (smallSignal backgroundSignal : ParentSignal S)
    (target : Fin S.count -> Option Bool) (fixed : Bool) (forced : target w.actionSeed = some fixed)
    (event : Event S.binary.Assignment) :
    (HedgeChannelTable.eventNumerator G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) target event : Int) =
      (HedgeChannelTable.eventNumerator G (channelCount w) (leftTables w)
        (leftSignals w rich smallSignal backgroundSignal) target event : Int) +
        projectedEventChange w smallSignal backgroundSignal target event :=
  eventNumerators_difference_of_action w rich smallSignal backgroundSignal target fixed forced event

/-- The exact change relevant to an original binary conditional cell.
The first projection is its full numerator cylinder; the second is its
conditioning cylinder.  Equal conditioning masses are not assumed. -/
def normalizedCellChange (w : HedgeWitness G query.jointNumerator)
    (rich : ObservedSignature.ValueRich S) (smallSignal backgroundSignal : ParentSignal S)
    (reference : S.binary.Assignment) : Int :=
  let kernel := (binaryConditionalQuery query).operationKernel
  let target := kernel.intervention reference
  let numerator := kernel.numeratorEvent reference
  let condition := kernel.conditionEvent reference
  projectedEventChange w smallSignal backgroundSignal target numerator *
      (HedgeChannelTable.eventNumerator G (channelCount w) (leftTables w)
        (leftSignals w rich smallSignal backgroundSignal) target condition : Int) -
    (HedgeChannelTable.eventNumerator G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) target numerator : Int) *
      projectedEventChange w smallSignal backgroundSignal target condition

/-- The normalized change is zero exactly when the two literal conditional
cross-products agree.  This is a necessary and sufficient arithmetic
criterion, not only a sufficient positivity bound on one numerator term. -/
theorem normalizedCellChange_eq_zero_iff (w : HedgeWitness G query.jointNumerator)
    (rich : ObservedSignature.ValueRich S) (smallSignal backgroundSignal : ParentSignal S)
    (reference : S.binary.Assignment) :
    normalizedCellChange w rich smallSignal backgroundSignal reference = 0 ↔
      HedgeChannelTable.eventNumerator G (channelCount w) (leftTables w)
          (leftSignals w rich smallSignal backgroundSignal)
          ((binaryConditionalQuery query).operationKernel.intervention reference)
          ((binaryConditionalQuery query).operationKernel.numeratorEvent reference) *
        HedgeChannelTable.eventNumerator G (channelCount w) (rightTables w)
          (rightSignals w smallSignal backgroundSignal)
          ((binaryConditionalQuery query).operationKernel.intervention reference)
          ((binaryConditionalQuery query).operationKernel.conditionEvent reference) =
      HedgeChannelTable.eventNumerator G (channelCount w) (rightTables w)
          (rightSignals w smallSignal backgroundSignal)
          ((binaryConditionalQuery query).operationKernel.intervention reference)
          ((binaryConditionalQuery query).operationKernel.numeratorEvent reference) *
        HedgeChannelTable.eventNumerator G (channelCount w) (leftTables w)
          (leftSignals w rich smallSignal backgroundSignal)
          ((binaryConditionalQuery query).operationKernel.intervention reference)
          ((binaryConditionalQuery query).operationKernel.conditionEvent reference) := by
  have forced : (binaryConditionalQuery query).operationKernel.intervention reference w.actionSeed =
      some (reference w.actionSeed) := by
    have acted : query.action w.actionSeed = true := w.actionSeed_in_action
    simp only [binaryConditionalQuery, ConditionalKernelQuery.binary, ConditionalKernelQuery.operationKernel,
      Kernel.intervention, acted, if_true]
  have joint := eventNumerator_change w rich smallSignal backgroundSignal _ _ forced
    ((binaryConditionalQuery query).operationKernel.numeratorEvent reference)
  have condition := eventNumerator_change w rich smallSignal backgroundSignal _ _ forced
    ((binaryConditionalQuery query).operationKernel.conditionEvent reference)
  have cross := FiniteRatioPerturbation.cross_eq_iff_balanced _ _ _ _ _ _ joint condition
  dsimp only [normalizedCellChange]
  constructor
  · intro zero
    apply cross.mpr
    omega
  · intro equal
    have balanced := cross.mp equal
    omega

/-! ## Actual supported kernel cells of the installed models -/

private theorem conditional_denominator_positive (w : HedgeWitness G query.jointNumerator)
    (tables : Fin S.count -> BooleanChannelTable (Fin (channelCount w)))
    (signals : HedgeChannelTable.Signals G (channelCount w)) (reference : S.binary.Assignment) :
    0 < HedgeChannelTable.eventNumerator G (channelCount w) tables signals
      ((binaryConditionalQuery query).operationKernel.intervention reference)
      ((binaryConditionalQuery query).operationKernel.conditionEvent reference) :=
  HedgeChannelTable.conditionalDenominator_positive G (channelCount w) tables signals
    (binaryConditionalQuery query).operationKernel reference

private noncomputable def conditional_cell (w : HedgeWitness G query.jointNumerator)
    (tables : Fin S.count -> BooleanChannelTable (Fin (channelCount w)))
    (signals : HedgeChannelTable.Signals G (channelCount w)) (reference : S.binary.Assignment) :
    ProbabilityResult.Equivalent
      ((binaryConditionalQuery query).sourceTerm.denote
        (HedgeChannelTable.model G (channelCount w) tables signals) reference)
      (some ⟨HedgeChannelTable.eventNumerator G (channelCount w) tables signals
          ((binaryConditionalQuery query).operationKernel.intervention reference)
          ((binaryConditionalQuery query).operationKernel.numeratorEvent reference),
        HedgeChannelTable.eventNumerator G (channelCount w) tables signals
          ((binaryConditionalQuery query).operationKernel.intervention reference)
          ((binaryConditionalQuery query).operationKernel.conditionEvent reference),
        conditional_denominator_positive w tables signals reference⟩) :=
  HedgeChannelTable.conditionalCell G (channelCount w) tables signals
    (binaryConditionalQuery query).operationKernel reference

/-- A nonzero normalized change separates the actual Boolean source cell.
This retains the supplied reference as data for the original-alphabet lift;
no further finite search through the installed model probabilities is needed. -/
theorem binary_conditionalCell_separated
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (reference : S.binary.Assignment)
    (nonzero : normalizedCellChange w rich smallSignal backgroundSignal reference ≠ 0) :
    Not (Nonempty (ProbabilityResult.Equivalent
      (query.binary.sourceTerm.denote (leftModel w rich smallSignal backgroundSignal) reference)
      (query.binary.sourceTerm.denote (rightModel w smallSignal backgroundSignal) reference))) := by
  intro supplied
  rcases supplied with ⟨same⟩
  have presented := ProbabilityResult.trans
    (ProbabilityResult.symm (conditional_cell w (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) reference))
    (ProbabilityResult.trans same (conditional_cell w (rightTables w)
      (rightSignals w smallSignal backgroundSignal) reference))
  cases presented with
  | value cross =>
      exact nonzero ((normalizedCellChange_eq_zero_iff w rich smallSignal backgroundSignal reference).mpr cross)

/-- Zero normalized change gives agreement of the actual supported source
cell.  This is the converse of the separating arithmetic criterion, with
the literal positive conditioning masses supplied by the installed SCMs.
Neither mass is assumed equal to the other, and undefined cells are not
silently replaced by zero-valued ratios. -/
noncomputable def binaryConditionalCellEquivalentOfNormalizedCellChangeZero
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (reference : S.binary.Assignment)
    (zero : normalizedCellChange w rich smallSignal backgroundSignal reference = 0) :
    ProbabilityResult.Equivalent
      (query.binary.sourceTerm.denote (leftModel w rich smallSignal backgroundSignal) reference)
      (query.binary.sourceTerm.denote (rightModel w smallSignal backgroundSignal) reference) := by
  refine ProbabilityResult.trans
    (conditional_cell w (leftTables w) (leftSignals w rich smallSignal backgroundSignal) reference)
    (ProbabilityResult.trans
      ?_
      (ProbabilityResult.symm
        (conditional_cell w (rightTables w) (rightSignals w smallSignal backgroundSignal) reference)))
  exact .value ((normalizedCellChange_eq_zero_iff w rich smallSignal backgroundSignal reference).mp zero)

/-- The complete finite criterion characterizes agreement of the whole
Boolean conditional in this installed family.  All cells are genuinely
supported by each model's observational positivity.  In the reverse
direction a supplied kernel comparison is inspected only propositionally;
in the forward construction the cell proof is built from its actual masses,
without choosing proof data out of a propositional existence statement.

This characterization can certify a family obstruction: if every change is
zero, no source reference in these two models separates the conditional.
That does not make the query identifiable in the full graph model class. -/
theorem binary_conditionals_equivalent_iff_normalizedCellChanges_zero
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) :
    query.binary.ValueEquivalent (leftModel w rich smallSignal backgroundSignal)
        (rightModel w smallSignal backgroundSignal) ↔
      forall reference, normalizedCellChange w rich smallSignal backgroundSignal reference = 0 := by
  constructor
  · intro equivalent reference
    rcases equivalent reference
      ((models_positive w rich smallSignal backgroundSignal).1.kernelPositiveSupportedValue
        query.binary.operationKernel reference).toSupported
      ((models_positive w rich smallSignal backgroundSignal).2.kernelPositiveSupportedValue
        query.binary.operationKernel reference).toSupported with ⟨same⟩
    have presented := ProbabilityResult.trans
      (ProbabilityResult.symm (conditional_cell w (leftTables w)
        (leftSignals w rich smallSignal backgroundSignal) reference))
      (ProbabilityResult.trans same (conditional_cell w (rightTables w)
        (rightSignals w smallSignal backgroundSignal) reference))
    cases presented with
    | value cross =>
        exact (normalizedCellChange_eq_zero_iff w rich smallSignal backgroundSignal reference).mpr cross
  · intro zero reference _leftSupported _rightSupported
    exact ⟨binaryConditionalCellEquivalentOfNormalizedCellChangeZero w rich smallSignal backgroundSignal
      reference (zero reference)⟩

/-- A genuinely nonzero normalized cell change supplies an actual positive
Boolean conditional countermodel, with arbitrary typed parent signals and
the whole original action, outcome and conditioner.  The evidence supports
are proved from the actual installed positive models.  No semantic gap or
equal-denominator premise is supplied separately.

This is the Boolean source boundary for alternative terminal signal
constructions.  The next constructor transports the same source cell to the
original alphabet; neither constructor assumes that the displayed finite
arithmetic premise holds at every terminal. -/
noncomputable def binaryConditionalCounterexampleOfNormalizedCellChange
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (reference : S.binary.Assignment)
    (nonzero : normalizedCellChange w rich smallSignal backgroundSignal reference ≠ 0) :
    ConditionalCounterexampleIn (GraphModelClass.positive G.binary) (binaryConditionalQuery query) where
  left := leftModel w rich smallSignal backgroundSignal
  right := rightModel w smallSignal backgroundSignal
  left_mem := ⟨(models_compatible w rich smallSignal backgroundSignal).1,
    (models_positive w rich smallSignal backgroundSignal).1⟩
  right_mem := ⟨(models_compatible w rich smallSignal backgroundSignal).2,
    (models_positive w rich smallSignal backgroundSignal).2⟩
  observationally_equal := models_observationallyEquivalent w rich smallSignal backgroundSignal
  query_separated := by
    intro equivalent
    exact binary_conditionalCell_separated w rich smallSignal backgroundSignal reference nonzero
      (equivalent reference
      ((models_positive w rich smallSignal backgroundSignal).1.kernelPositiveSupportedValue
        (binaryConditionalQuery query).operationKernel reference).toSupported
      ((models_positive w rich smallSignal backgroundSignal).2.kernelPositiveSupportedValue
        (binaryConditionalQuery query).operationKernel reference).toSupported)

/-- A nonzero complete normalized cell change constructs a positive
counterexample for the unchanged original full-alphabet conditional query.
The explicit source reference determines the coordinate recoding; encoding
and independent private refinement preserve that cell in each actual model.
All original labels receive positive mass, and the original source action
values are recovered by decoding the final all-second intervention.

No equality of conditioning marginals, protected refinement pivot, extra
observed coordinate or searched auxiliary source cell is required.  An
application still needs typed signals and a source reference with a nonzero
normalized change.  Their existence is not universal for this installation;
latent-entry terminals may require a different Boolean countermodel pair. -/
noncomputable def conditionalCounterexampleOfNormalizedCellChange
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (reference : S.binary.Assignment)
    (nonzero : normalizedCellChange w rich smallSignal backgroundSignal reference ≠ 0) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  ObservedValueRefinement.positiveConditionalCounterexampleOfBinaryCell query rich
    (leftModel w rich smallSignal backgroundSignal) (rightModel w smallSignal backgroundSignal)
    (models_compatible w rich smallSignal backgroundSignal).1
    (models_compatible w rich smallSignal backgroundSignal).2
    (models_positive w rich smallSignal backgroundSignal).1
    (models_positive w rich smallSignal backgroundSignal).2
    (models_observationallyEquivalent w rich smallSignal backgroundSignal) reference
    (binary_conditionalCell_separated w rich smallSignal backgroundSignal reference nonzero)

end HedgeChannelInstallation
end Causality
end Thesis
