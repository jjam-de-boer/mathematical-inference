import Thesis.CausalTransport.HedgeChannelLikelihood

namespace Thesis
namespace Causality
namespace HedgeChannelTable

open Probability

/-!
# Actual supported conditional cells of arbitrary positive channel models

The likelihood theorem presents every intervened event on one common
positive denominator.  A conditional cell divides its numerator cylinder
by its own conditioning cylinder, so that common model denominator cancels.
The two literal event numerators are the resulting ratio presentation.

This argument applies to every channel count and every typed centre family,
including centres which read independent environment bits.  It requires no
hedge, nonempty action, equal capacities between models, or matched evidence
marginal.  The no-action branch is covered by the intrinsic kernel event
theorem, which identifies its actual distribution with the no-intervention
evaluation.  All conditioning cylinders are supported at the reference's
own intervention by the model's complete observational positivity.

Cross-product comparison is therefore an exact criterion for actual cell
agreement.  The constructive cell adapter below builds comparison data from
that criterion directly; it never chooses a proof out of `Nonempty`.
This is the shared semantic boundary for the original and widened channel
countermodel families, not an existence theorem for separating signals.
-/

variable {S : ObservedSignature.{0}}

/-- The literal event numerator presents the actual kernel distribution's
event probability, including an empty action and conflicting forced cells. -/
theorem kernel_eventNumerator (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (kernel : Kernel S.binary) (reference : S.binary.Assignment) (event : Event S.binary.Assignment) :
    QProb.Equiv (((kernel.distribution (model G channels tables signals) reference).probVal event))
      ⟨eventNumerator G channels tables signals (kernel.intervention reference) event,
        likelihoodDenominator G channels tables (kernel.intervention reference),
        likelihoodDenominator_positive G channels tables (kernel.intervention reference)⟩ := by
  refine QProb.equiv_trans (kernel.distribution_probVal (model G channels tables signals) reference event) ?_
  exact QProb.equiv_trans
    (QProb.equiv_symm ((model G channels tables signals).interventionalValue_eq
      (kernel.intervention reference) event))
    (model_interventional_event G channels tables signals (kernel.intervention reference) event)

/-- Every actual conditioning cylinder has a positive literal numerator at
its own reference-compatible intervention.  No equal-marginal premise or
soundness theorem supplies this intrinsic support fact. -/
theorem conditionalDenominator_positive (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (kernel : Kernel S.binary) (reference : S.binary.Assignment) :
    0 < eventNumerator G channels tables signals (kernel.intervention reference) (kernel.conditionEvent reference) :=
  (QProb.equiv_num_pos_iff (kernel_eventNumerator G channels tables signals kernel reference _)).mp
    ((model_positive G channels tables signals).kernel_cylinder_positive kernel kernel.condition reference)

/-- The actual partial kernel cell is defined and has precisely the ratio
of its two event numerators.  Each model retains its own conditioning mass;
no source enumeration beyond the established likelihood formula is reduced. -/
noncomputable def conditionalCell (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (kernel : Kernel S.binary) (reference : S.binary.Assignment) :
    ProbabilityResult.Equivalent (kernel.denote (model G channels tables signals) reference)
      (some ⟨eventNumerator G channels tables signals (kernel.intervention reference) (kernel.numeratorEvent reference),
        eventNumerator G channels tables signals (kernel.intervention reference) (kernel.conditionEvent reference),
        conditionalDenominator_positive G channels tables signals kernel reference⟩) := by
  unfold Kernel.denote
  refine ProbabilityResult.trans (ProbabilityResult.divide_congr
    (.value (kernel_eventNumerator G channels tables signals kernel reference _))
    (.value (kernel_eventNumerator G channels tables signals kernel reference _))) ?_
  rw [ProbabilityResult.divide, dif_pos (conditionalDenominator_positive G channels tables signals kernel reference)]
  apply ProbabilityResult.Equivalent.value
  change _ * _ * _ = _ * (_ * _)
  ac_rfl

/-- Build actual supported cell comparison from the two literal cross-
products.  Different table capacities and different evidence masses are
allowed; the common likelihood denominator cancels separately in each model. -/
noncomputable def conditionalCellEquivalentOfCross
    (G : ObservedGraph S) (channels : Nat)
    (left right : Fin S.count -> BooleanChannelTable (Fin channels)) (leftSignals rightSignals : Signals G channels)
    (kernel : Kernel S.binary) (reference : S.binary.Assignment)
    (cross : eventNumerator G channels left leftSignals (kernel.intervention reference) (kernel.numeratorEvent reference) *
        eventNumerator G channels right rightSignals (kernel.intervention reference) (kernel.conditionEvent reference) =
      eventNumerator G channels right rightSignals (kernel.intervention reference) (kernel.numeratorEvent reference) *
        eventNumerator G channels left leftSignals (kernel.intervention reference) (kernel.conditionEvent reference)) :
    ProbabilityResult.Equivalent (kernel.denote (model G channels left leftSignals) reference)
      (kernel.denote (model G channels right rightSignals) reference) := by
  refine ProbabilityResult.trans (conditionalCell G channels left leftSignals kernel reference)
    (ProbabilityResult.trans ?_
      (ProbabilityResult.symm (conditionalCell G channels right rightSignals kernel reference)))
  exact .value cross

/-- Agreement of the actual supported conditional cell is equivalent to
equality of the complete natural cross-products.  This is necessary as well
as sufficient, and concerns these actual SCMs rather than abstract polynomials. -/
theorem conditionalCell_equivalent_iff_cross
    (G : ObservedGraph S) (channels : Nat)
    (left right : Fin S.count -> BooleanChannelTable (Fin channels)) (leftSignals rightSignals : Signals G channels)
    (kernel : Kernel S.binary) (reference : S.binary.Assignment) :
    Nonempty (ProbabilityResult.Equivalent (kernel.denote (model G channels left leftSignals) reference)
      (kernel.denote (model G channels right rightSignals) reference)) ↔
      eventNumerator G channels left leftSignals (kernel.intervention reference) (kernel.numeratorEvent reference) *
          eventNumerator G channels right rightSignals (kernel.intervention reference) (kernel.conditionEvent reference) =
        eventNumerator G channels right rightSignals (kernel.intervention reference) (kernel.numeratorEvent reference) *
          eventNumerator G channels left leftSignals (kernel.intervention reference) (kernel.conditionEvent reference) := by
  constructor
  · intro supplied
    rcases supplied with ⟨same⟩
    have presented := ProbabilityResult.trans
      (ProbabilityResult.symm (conditionalCell G channels left leftSignals kernel reference))
      (ProbabilityResult.trans same (conditionalCell G channels right rightSignals kernel reference))
    cases presented with
    | value cross => exact cross
  · intro cross
    exact ⟨conditionalCellEquivalentOfCross G channels left right leftSignals rightSignals kernel reference cross⟩

end HedgeChannelTable
end Causality
end Thesis
