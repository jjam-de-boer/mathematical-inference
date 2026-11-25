import Thesis.Causality.QualitativeExperimentRepresentation
import Thesis.Causality.QualitativeDoCalculus

namespace Thesis.Causality.CausalExperimentData
open Probability Probability.ClaytonWaddington QualitativeDoCalculus
universe u v
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Representation preserves comparisons and partial conditionals

The representation theorem concerns full experimental laws, rather than raw
urn records. These consequences spell out what that means for the observer
and for qualitative reasoning. They apply to every explicit completion of
unexercised recipe rows. Repeated labels, different urn sizes and zero-weight
record presentations cannot change the conclusions.

A supported zero remains a defined plausibility. A null conditioner remains
`none`; no completion of an unused recipe row completes that conditional.
The final game round trip preserves laws, not a joint assignment of responses
across mutually exclusive hypothetical experiments.
-/

theorem realize_support_iff (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (completion : data.NullCompletion) (setting) (evidence : Event data.Assignment) :
    0 < (data.slice setting).probNum evidence ↔
      0 < ((data.realizeWithCompletion completion).fullUrn setting).probNum evidence :=
  QProb.equiv_num_pos_iff (data.realizeWithCompletion_preserves_full scale rules completion setting evidence)

/-- The full experimental event plausibility is unchanged by reconstruction. -/
theorem realize_eventPlaus (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (completion : data.NullCompletion) (setting) (event : Event data.Assignment) :
    scale.eqv (data.eventPlaus scale setting event)
      (((data.realizeWithCompletion completion).experimentData data.order).eventPlaus scale setting event) :=
  (scale.eqv_iff_sameRatio _ _).mpr
    (data.realizeWithCompletion_preserves_full scale rules completion setting event)

/-- This is preservation of the comparison relation across different
experiments, not merely equality of each experiment's normalization. -/
theorem realize_comparisons (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (completion : data.NullCompletion) (first second) (left right : Event data.Assignment) :
    scale.eqv (data.eventPlaus scale first left) (data.eventPlaus scale second right) ↔
      scale.eqv
        (((data.realizeWithCompletion completion).experimentData data.order).eventPlaus scale first left)
        (((data.realizeWithCompletion completion).experimentData data.order).eventPlaus scale second right) := by
  have leftAgreement := data.realize_eventPlaus scale rules completion first left
  have rightAgreement := data.realize_eventPlaus scale rules completion second right
  constructor
  · intro equal
    exact scale.eqv_trans (scale.eqv_symm leftAgreement) (scale.eqv_trans equal rightAgreement)
  · intro equal
    exact scale.eqv_trans leftAgreement (scale.eqv_trans equal (scale.eqv_symm rightAgreement))

theorem realize_strict_comparisons (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (completion : data.NullCompletion) (first second) (left right : Event data.Assignment) :
    scale.lt (data.eventPlaus scale first left) (data.eventPlaus scale second right) ↔
      scale.lt
        (((data.realizeWithCompletion completion).experimentData data.order).eventPlaus scale first left)
        (((data.realizeWithCompletion completion).experimentData data.order).eventPlaus scale second right) := by
  have leftAgreement := data.realize_eventPlaus scale rules completion first left
  have rightAgreement := data.realize_eventPlaus scale rules completion second right
  exact ⟨scale.lt_respects_eqv leftAgreement rightAgreement,
    scale.lt_respects_eqv (scale.eqv_symm leftAgreement) (scale.eqv_symm rightAgreement)⟩

/-- Both branches of the partial interface are preserved. In the supported
branch the outcome event may have mass zero. The unsupported branch asserts
`none` on both sides, without evaluating any null-evidence conditional. -/
theorem realize_conditional (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (completion : data.NullCompletion) (setting) (event evidence : Event data.Assignment) :
    KernelPlausEqv scale (data.conditional scale setting event evidence)
      (((data.realizeWithCompletion completion).experimentData data.order).conditional scale setting event evidence) := by
  let actual := (data.realizeWithCompletion completion).experimentData data.order
  change KernelPlausEqv scale (data.conditional scale setting event evidence)
    (actual.conditional scale setting event evidence)
  have support := data.realize_support_iff scale rules completion setting evidence
  by_cases positive : 0 < (data.slice setting).probNum evidence
  · have otherPositive : 0 < (actual.slice setting).probNum evidence := support.mp positive
    simp only [conditional, dif_pos positive, dif_pos otherPositive]
    apply KernelPlausEqv.defined
    apply (scale.eqv_iff_sameRatio _ _).mpr
    exact UrnProb.condVal_congr_of_probVal _ _
      (data.realizeWithCompletion_preserves_full scale rules completion setting)
      event evidence positive otherPositive
  · have otherNotPositive : ¬ 0 < (actual.slice setting).probNum evidence :=
      fun otherPositive => positive (support.mpr otherPositive)
    simp only [conditional, dif_neg positive, dif_neg otherNotPositive]
    exact .unsupported

theorem realize_conditional_none_iff (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (completion : data.NullCompletion) (setting) (event evidence : Event data.Assignment) :
    data.conditional scale setting event evidence = none ↔
      ((data.realizeWithCompletion completion).experimentData data.order).conditional scale setting event evidence = none := by
  rw [conditional_none_iff, conditional_none_iff]
  exact not_congr (data.realize_support_iff scale rules completion setting evidence)

/-- The recorded observer sees the original law after reconstruction. The
proof projects an equality of full laws, retaining hidden common causes. -/
theorem realize_recorded_law (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (completion : data.NullCompletion) (setting) (event : Event S.Assignment) :
    QProb.Equiv ((data.recordedLaw setting).probVal event)
      (((data.realizeWithCompletion completion).law setting).probVal event) := by
  let game := data.realizeWithCompletion completion
  refine QProb.equiv_trans (FiniteProbRecord.ofUrn_agrees _ _) ?_
  refine QProb.equiv_trans ((data.slice setting).probVal_map data.record event) ?_
  refine QProb.equiv_trans (data.realizeWithCompletion_preserves_full scale rules completion setting
    (fun assignment => event (data.record assignment))) ?_
  refine QProb.equiv_trans (QProb.equiv_symm ((game.fullUrn setting).probVal_map data.record event)) ?_
  exact QProb.equiv_symm (game.recordUrn_agrees setting event)

end Thesis.Causality.CausalExperimentData

namespace Thesis.Causality.CausalUrnGame
open Probability Probability.ClaytonWaddington
universe u v
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-- **Game → abstract system → game.** Re-extraction need not recover the
original recipe cells or response-table coupling. It recovers every full
experimental event law, including all unrecorded coordinates and zeros. -/
theorem reconstruction_roundTrip (game : CausalUrnGame S P)
    (order : CausalOrder P.hiddenDAG) (scale : QualitativeUrnScale.{v})
    (setting) (event : Event game.FullAssignment) :
    QProb.Equiv ((game.fullUrn setting).probVal event)
      ((((game.experimentData order).realize).fullUrn setting).probVal event) :=
  (game.experimentData order).realize_preserves_full scale (game.qualitativeRules order scale) setting event

end Thesis.Causality.CausalUrnGame
