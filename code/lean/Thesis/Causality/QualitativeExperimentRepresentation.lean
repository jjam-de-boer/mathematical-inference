import Thesis.Causality.QualitativeExperimentRecipes
import Thesis.Causality.CausalUrnExperimentalLaw

namespace Thesis.Causality.CausalExperimentData
open Probability Probability.ClaytonWaddington
universe u v
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Qualitative rules reconstruct one stable causal urn game

Each supplied whole-experiment urn is only ordinary probability data. The
approved requirements determine supported local rows, and complete earlier
conditionals determine the full law by successive cylinder extension.
Neither factorization nor a causal soundness certificate is supplied.

Null histories have only null extensions, so their conditionals are never
evaluated. Set variables are constant on a probability-one event, allowing
zero-weight exceptions in record presentations. Every explicit completion of
the unexercised rows yields the same admitted experimental laws. Unrecorded
values remain part of those laws until the final record projection.
-/

theorem history_conditional_recipe (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (rules : QualitativeCausalRules data scale) (completion : data.NullCompletion)
    (setting) (child) (reference : data.Assignment) (event : Event (data.Value child))
    (unforced : data.forcedAt setting child = none)
    (supported : 0 < (data.slice setting).probNum (data.history child reference)) :
    QProb.Equiv ((data.slice setting).condVal (data.nodeEvent child event) (data.history child reference) supported)
      ((data.recipeWithCompletion completion child (data.parents child reference)).probVal event) := by
  have sufficiency := rules.parentSufficiency setting child reference event unforced supported
  have numerical := (data.conditionalPlaus_eqv_iff scale setting setting _ _ _ _ _ _).mp sufficiency
  have recipe := data.recipe_agrees scale rules completion setting child (data.parents child reference) event
    unforced (data.parents_supported_of_history setting child reference supported)
  exact QProb.equiv_trans numerical (QProb.equiv_symm recipe)

/-- A supported conditional of a set variable is a Boolean constant. It is
a defined zero if the tested event rejects the forced value. -/
theorem conditional_of_forced (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (rules : QualitativeCausalRules data scale) (setting) (child) (value : data.Value child)
    (forced : data.forcedAt setting child = some value)
    (evidence : Event data.Assignment) (event : Event (data.Value child))
    (supported : (FiniteProbRecord.ofUrn (data.slice setting)).EventPositive evidence) :
    QProb.Equiv (((FiniteProbRecord.ofUrn (data.slice setting)).conditionOn evidence supported).probVal
      (data.nodeEvent child event)) (if event value then QProb.one else QProb.zero) := by
  let sure := data.nodeEvent child (fun actual => decide (actual = value))
  have effectiveness := rules.effectiveness setting child value forced
  have numeric := (data.eventPlaus_eqv_iff scale setting setting sure topEvent).mp effectiveness
  have full : QProb.Equiv ((FiniteProbRecord.ofUrn (data.slice setting)).probVal sure) QProb.one :=
    QProb.equiv_trans (FiniteProbRecord.ofUrn_agrees (data.slice setting) sure)
      (QProb.equiv_trans numeric (data.slice setting).normalization)
  apply FiniteProbRecord.conditional_constant_on_full_event _ sure evidence _ (event value) full _ supported
  intro sample selected
  have same : sample child = value := of_decide_eq_true selected
  exact congrArg event same

theorem history_record_recipe (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (rules : QualitativeCausalRules data scale) (completion : data.NullCompletion)
    (setting) (child) (reference : data.Assignment) (event : Event (data.Value child))
    (unforced : data.forcedAt setting child = none)
    (supported : (FiniteProbRecord.ofUrn (data.slice setting)).EventPositive (data.history child reference)) :
    QProb.Equiv (((FiniteProbRecord.ofUrn (data.slice setting)).conditionOn
      (data.history child reference) supported).probVal (data.nodeEvent child event))
      ((data.recipeWithCompletion completion child (data.parents child reference)).probVal event) := by
  have urnSupported := (FiniteProbRecord.ofUrn_support_iff _ _).mp supported
  exact QProb.equiv_trans (FiniteProbRecord.conditionOn_ofUrn_equiv _ _ _ supported urnSupported)
    (data.history_conditional_recipe scale rules completion setting child reference event unforced urnSupported)

/-- **Abstract system → game, full laws.** Every full-assignment event has
its original probability in every hard experiment. This holds for every
explicit completion, without strict positivity or extra hidden settings. -/
theorem realizeWithCompletion_preserves_full (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (completion : data.NullCompletion) (setting : HardIntervention S) (event : Event data.Assignment) :
    QProb.Equiv ((data.slice setting).probVal event)
      (((data.realizeWithCompletion completion).fullUrn setting).probVal event) := by
  let game := data.realizeWithCompletion completion
  let actual := game.experimentData data.order
  let left := FiniteProbRecord.ofUrn (data.slice setting)
  let right := FiniteProbRecord.ofUrn (game.fullUrn setting)
  letI : (node : Fin P.hiddenDAG.count) → DecidableEq (data.Value node) := data.valueEq
  have agreement : OrderedHistory.ForwardAgreement data.order.nodes left right := by
    intro past child future splitNodes reference
    have earlier := data.order.earlier_eq_of_split past child future splitNodes
    have sameHistory : OrderedHistory.history past reference = data.history child reference := by
      unfold history
      rw [earlier]
    let childEvent : Event (data.Value child) := fun value => decide (value = reference child)
    have sameCoordinate : OrderedHistory.coordinate child reference = data.nodeEvent child childEvent := rfl
    rw [sameHistory, sameCoordinate]
    intro leftPositive rightPositive
    change left.EventPositive (data.history child reference) at leftPositive
    change right.EventPositive (data.history child reference) at rightPositive
    cases forced : data.forcedAt setting child with
    | some value =>
        have leftLaw := data.conditional_of_forced scale rules setting child value forced
          (data.history child reference) childEvent leftPositive
        have actualForced : actual.forcedAt setting child = some value := forced
        have rightLaw := actual.conditional_of_forced scale (game.qualitativeRules data.order scale)
          setting child value actualForced (data.history child reference) childEvent rightPositive
        exact QProb.equiv_trans leftLaw (QProb.equiv_symm rightLaw)
    | none =>
        have leftLaw := data.history_record_recipe scale rules completion setting child reference childEvent
          forced leftPositive
        have gameUnforced : game.forcedAt setting child = none := forced
        have rightSupported : 0 < (game.fullUrn setting).probNum (data.history child reference) :=
          (FiniteProbRecord.ofUrn_support_iff _ _).mp rightPositive
        have rightRaw := game.conditional_event_recipe data.order setting child gameUnforced
          (data.parents child reference) childEvent (data.history child reference)
          (data.history_dependsBefore child reference)
          (fun sample selected => data.history_implies_parent child reference sample selected |> of_decide_eq_true)
          rightSupported
        have rightLaw := QProb.equiv_trans
          (FiniteProbRecord.conditionOn_ofUrn_equiv _ _ _ rightPositive rightSupported) rightRaw
        exact QProb.equiv_trans leftLaw (QProb.equiv_symm rightLaw)
  have whole := OrderedHistory.probVal_equiv_of_forwardAgreement data.order.nodes data.order.complete
    left right agreement data.values data.complete event
  exact QProb.equiv_trans (QProb.equiv_symm (FiniteProbRecord.ofUrn_agrees (data.slice setting) event))
    (QProb.equiv_trans whole (FiniteProbRecord.ofUrn_agrees (game.fullUrn setting) event))

theorem realize_preserves_full (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (rules : QualitativeCausalRules data scale) (setting) (event : Event data.Assignment) :
    QProb.Equiv ((data.slice setting).probVal event) ((data.realize.fullUrn setting).probVal event) :=
  data.realizeWithCompletion_preserves_full scale rules data.defaultCompletion setting event

/-- Rule validity depends on complete event laws, not a particular finite
cell presentation. This transfers all supported conditionals as well. -/
theorem rules_of_slice_agreement (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (newSlice : HardIntervention S → UrnProb data.Assignment)
    (agree : ∀ setting event, QProb.Equiv ((data.slice setting).probVal event) ((newSlice setting).probVal event))
    (otherRules : QualitativeCausalRules { data with slice := newSlice } scale) : QualitativeCausalRules data scale := by
  let other : CausalExperimentData S P := { data with slice := newSlice }
  have eventAgreement : ∀ setting event,
      scale.eqv (data.eventPlaus scale setting event) (other.eventPlaus scale setting event) := by
    intro setting event
    exact (scale.eqv_iff_sameRatio _ _).mpr (agree setting event)
  have supportedAgreement : ∀ setting evidence,
      0 < (data.slice setting).probNum evidence ↔ 0 < (other.slice setting).probNum evidence := by
    intro setting evidence
    exact QProb.equiv_num_pos_iff (agree setting evidence)
  have conditionalAgreement : ∀ setting event evidence
      (firstSupported : 0 < (data.slice setting).probNum evidence)
      (secondSupported : 0 < (other.slice setting).probNum evidence),
      scale.eqv (data.conditionalPlaus scale setting event evidence firstSupported)
        (other.conditionalPlaus scale setting event evidence secondSupported) := by
    intro setting event evidence firstSupported secondSupported
    apply (scale.eqv_iff_sameRatio _ _).mpr
    exact UrnProb.condVal_congr_of_probVal _ _ (agree setting) event evidence firstSupported secondSupported
  constructor
  · intro setting child value forced
    exact scale.eqv_trans (eventAgreement setting _)
      (scale.eqv_trans (otherRules.effectiveness setting child value forced)
        (scale.eqv_symm (eventAgreement setting topEvent)))
  · intro setting child reference event unforced supported
    have otherSupported := (supportedAgreement setting (data.history child reference)).mp supported
    exact scale.eqv_trans (conditionalAgreement setting _ _ supported otherSupported)
      (scale.eqv_trans (otherRules.parentSufficiency setting child reference event unforced otherSupported)
        (scale.eqv_symm (conditionalAgreement setting _ _
          (data.parents_supported_of_history setting child reference supported)
          (other.parents_supported_of_history setting child reference otherSupported))))
  · intro first second child parents event firstUnforced secondUnforced firstSupported secondSupported
    have otherFirst := (supportedAgreement first (data.parentEvent child parents)).mp firstSupported
    have otherSecond := (supportedAgreement second (data.parentEvent child parents)).mp secondSupported
    exact scale.eqv_trans (conditionalAgreement first _ _ firstSupported otherFirst)
      (scale.eqv_trans (otherRules.experimentalStability first second child parents event
        firstUnforced secondUnforced otherFirst otherSecond)
        (scale.eqv_symm (conditionalAgreement second _ _ secondSupported otherSecond)))

/-- Two-way characterization: the canonical algorithm represents exactly
the full experimental laws satisfying the approved qualitative rules. -/
theorem qualitativeRules_iff_realization (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v}) :
    QualitativeCausalRules data scale ↔ ∀ setting event,
      QProb.Equiv ((data.slice setting).probVal event) ((data.realize.fullUrn setting).probVal event) := by
  constructor
  · intro rules setting event
    exact data.realize_preserves_full scale rules setting event
  · intro agree
    exact data.rules_of_slice_agreement scale data.realize.fullUrn agree
      (data.realize.qualitativeRules data.order scale)

/-- Different completions preserve the entire full law in every setting;
their unused recipe cells and counterfactual coupling need not be identical. -/
theorem completions_preserve_same_law (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (rules : QualitativeCausalRules data scale) (first second : data.NullCompletion)
    (setting) (event : Event data.Assignment) :
    QProb.Equiv (((data.realizeWithCompletion first).fullUrn setting).probVal event)
      (((data.realizeWithCompletion second).fullUrn setting).probVal event) :=
  QProb.equiv_trans (QProb.equiv_symm (data.realizeWithCompletion_preserves_full scale rules first setting event))
    (data.realizeWithCompletion_preserves_full scale rules second setting event)

def withOrder (data : CausalExperimentData S P) (order : CausalOrder P.hiddenDAG) : CausalExperimentData S P :=
  { data with order := order }

/-- Any compatible total order validates the same causal requirements.
Reconstruct the full laws once, then apply game → rules in the new order.
This asserts law-level invariance, not equality of raw game records. -/
theorem qualitativeRules_withOrder (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (rules : QualitativeCausalRules data scale) (order : CausalOrder P.hiddenDAG) :
    QualitativeCausalRules (data.withOrder order) scale := by
  apply (data.withOrder order).rules_of_slice_agreement scale data.realize.fullUrn
  · intro setting event
    exact data.realize_preserves_full scale rules setting event
  · exact data.realize.qualitativeRules order scale

theorem qualitativeRules_order_iff (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (order : CausalOrder P.hiddenDAG) :
    QualitativeCausalRules (data.withOrder order) scale ↔ QualitativeCausalRules data scale := by
  constructor
  · intro rules
    have back := (data.withOrder order).qualitativeRules_withOrder scale rules data.order
    have restored : (data.withOrder order).withOrder data.order = data := by cases data; rfl
    rw [restored] at back
    exact back
  · intro rules
    exact data.qualitativeRules_withOrder scale rules order

theorem realizations_order_same_law (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (rules : QualitativeCausalRules data scale) (first second : CausalOrder P.hiddenDAG)
    (setting) (event : Event data.Assignment) :
    QProb.Equiv (((data.withOrder first).realize.fullUrn setting).probVal event)
      (((data.withOrder second).realize.fullUrn setting).probVal event) :=
  QProb.equiv_trans
    (QProb.equiv_symm ((data.withOrder first).realize_preserves_full scale
      (data.qualitativeRules_withOrder scale rules first) setting event))
    ((data.withOrder second).realize_preserves_full scale
      (data.qualitativeRules_withOrder scale rules second) setting event)

end Thesis.Causality.CausalExperimentData
