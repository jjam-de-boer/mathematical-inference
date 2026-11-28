import Thesis.CausalTransport.CausalAbstractionInverse
import Thesis.Probability.Distros.PartialMomentConditionalBounds

/-!
# Supported fine conditional queries from coarse experimental laws

First optimize the evidence indicator. A null maximum proves that no
conditional value is available. A null minimum together with a positive
maximum yields both a supported and an undefined model. In the supported
case, optimize the ratio of the joint event to evidence mass on the
positive-denominator domain. Endpoints are realized by fine models, and an
undefined model remains visible even when the supported range is a point.
-/

namespace Thesis.Causality.CausalAbstractionInverse

open Probability Probability.Distros
open SharedResponse (Table)

variable {fine coarse : ObservedSignature.{0}}

namespace EventQuery

theorem evidence_of_responseLaw (query : EventQuery fine) (law : FiniteProbRecord (Table fine)) :
    QProb.Equiv ((SharedResponse.model fine law).prior.probVal
      (query.holds (SharedResponse.model fine law))) (law.probVal query.onTable) :=
  QProb.equiv_trans (QProb.equiv_symm (query.value_eq_probVal _)) (query.value_of_responseLaw law)

theorem responseLaw_evidence (query : EventQuery fine) (model : ExactModel fine) :
    QProb.Equiv ((SharedResponse.lawOf fine model).probVal query.onTable)
      (model.prior.probVal (query.holds model)) :=
  QProb.equiv_trans (query.responseLaw_value model) (query.value_eq_probVal model)

end EventQuery

namespace Specification

private theorem conditional_congr {A B : Type}
    (left : FiniteProbRecord A) (right : FiniteProbRecord B)
    (evidence : Event A) (event : Event A) (evidence' : Event B) (event' : Event B)
    (denominator : QProb.Equiv (left.probVal evidence) (right.probVal evidence'))
    (numerator : QProb.Equiv (left.probVal (fun a => evidence a && event a))
      (right.probVal (fun b => evidence' b && event' b)))
    (positive : left.EventPositive evidence) (positive' : right.EventPositive evidence') :
    QProb.Equiv ((left.conditionOn evidence positive).probVal event)
      ((right.conditionOn evidence' positive').probVal event') :=
  QProb.equiv_trans (left.conditionOn_probVal evidence event positive)
    (QProb.equiv_trans (QProb.div_congr numerator denominator positive positive')
      (QProb.equiv_symm (right.conditionOn_probVal evidence' event' positive')))

/-- A fine model witnessing that the causal conditioning event is usable. -/
structure SupportedModel (spec : Specification fine coarse) (evidence : EventQuery fine) where
  model : ExactModel fine
  fits : spec.Fits model
  positive : model.prior.EventPositive (evidence.holds model)

def SupportedModel.value {spec : Specification fine coarse} {evidence : EventQuery fine}
    (source : spec.SupportedModel evidence) (event : EventQuery fine) : QProb :=
  (source.model.prior.conditionOn (evidence.holds source.model) source.positive).probVal
    (event.holds source.model)

def supportedOfLaw (spec : Specification fine coarse) (evidence : EventQuery fine)
    (law : spec.problem.ConditionalLaw evidence.onTable) : spec.SupportedModel evidence where
  model := SharedResponse.model fine law.distro.record
  fits := spec.fits_of_responseFits law.distro.record
    ((spec.moments_iff_responseFits law.distro).mp law.moments)
  positive := (QProb.equiv_num_pos_iff (evidence.evidence_of_responseLaw law.distro.record)).mpr law.positive

theorem supportedOfLaw_value (spec : Specification fine coarse) (evidence event : EventQuery fine)
    (law : spec.problem.ConditionalLaw evidence.onTable) :
    QProb.Equiv ((spec.supportedOfLaw evidence law).value event) (law.value event.onTable) :=
  conditional_congr _ _ _ _ _ _ (evidence.evidence_of_responseLaw law.distro.record)
    ((EventQuery.conj evidence event).evidence_of_responseLaw law.distro.record) _ _

def lawOfSupported {spec : Specification fine coarse} {evidence : EventQuery fine}
    (source : spec.SupportedModel evidence) : spec.problem.ConditionalLaw evidence.onTable where
  distro := ⟨SharedResponse.lawOf fine source.model⟩
  support := spec.table_support _
  moments := (spec.moments_iff_responseFits _).mpr (spec.responseFits_of_fits source.model source.fits)
  positive := (QProb.equiv_num_pos_iff (evidence.responseLaw_evidence source.model)).mpr source.positive

theorem lawOfSupported_value {spec : Specification fine coarse} {evidence : EventQuery fine}
    (source : spec.SupportedModel evidence) (event : EventQuery fine) :
    QProb.Equiv ((lawOfSupported source).value event.onTable) (source.value event) :=
  conditional_congr _ _ _ _ _ _ (evidence.responseLaw_evidence source.model)
    ((EventQuery.conj evidence event).responseLaw_evidence source.model) _ _

/-- Sharp values refer to the supported compatible models and include
actual models at both endpoints. -/
structure ConditionalBounds (spec : Specification fine coarse) (evidence event : EventQuery fine) where
  lower : spec.SupportedModel evidence
  upper : spec.SupportedModel evidence
  bounds : ∀ source : spec.SupportedModel evidence,
    QProb.LE (lower.value event) (source.value event) ∧ QProb.LE (source.value event) (upper.value event)

/-- A point among supported models leaves the separate support report
in force. It can coexist with compatible models where the answer is undefined. -/
theorem ConditionalBounds.point {spec : Specification fine coarse} {evidence event : EventQuery fine}
    (sharp : spec.ConditionalBounds evidence event)
    (same : QProb.Equiv (sharp.lower.value event) (sharp.upper.value event))
    (model : spec.SupportedModel evidence) :
    QProb.Equiv (model.value event) (sharp.lower.value event) :=
  Nat.le_antisymm
    (QProb.le_congr (QProb.equiv_refl _) (QProb.equiv_symm same) (sharp.bounds model).2)
    (sharp.bounds model).1

def conditionalBoundsOfRange (spec : Specification fine coarse) (evidence event : EventQuery fine)
    (sharp : spec.problem.ConditionalRange evidence.onTable event.onTable) :
    spec.ConditionalBounds evidence event where
  lower := spec.supportedOfLaw evidence sharp.lower
  upper := spec.supportedOfLaw evidence sharp.upper
  bounds := by
    intro source
    have bounded := sharp.bounds (lawOfSupported source)
    exact ⟨QProb.le_congr (QProb.equiv_symm (spec.supportedOfLaw_value evidence event sharp.lower))
      (lawOfSupported_value source event) bounded.1,
      QProb.le_congr (lawOfSupported_value source event)
      (QProb.equiv_symm (spec.supportedOfLaw_value evidence event sharp.upper)) bounded.2⟩

/-- Evidence can be absent in compatible models even when there are
supported models. Keep the witness in that case. -/
inductive NullEvidence (spec : Specification fine coarse) (evidence : EventQuery fine) where
  | possible (model : ExactModel fine) (fits : spec.Fits model) (zero : (evidence.value model).num = 0)
  | impossible (positive : ∀ model, spec.Fits model → 0 < (evidence.value model).num)

private theorem positive_of_le {p q : QProb} (positive : 0 < p.num) (ordered : QProb.LE p q) :
    0 < q.num := by
  rcases Nat.eq_zero_or_pos q.num with zero | positive'
  · change p.num * q.den ≤ q.num * p.den at ordered
    rw [zero, Nat.zero_mul] at ordered
    exact False.elim (Nat.not_lt_of_ge ordered (Nat.mul_pos positive q.den_pos))
  · exact positive'

private def nullEvidenceOfBounds {spec : Specification fine coarse} {query : EventQuery fine}
    (sharp : spec.QueryBounds query) : spec.NullEvidence query :=
  if minimum : 0 < (query.value sharp.lowerModel).num then
    .impossible (fun model fits => positive_of_le minimum
      ((SignedRatio.toSignedRatio_le_iff _ _).mp
        ((SignedRatio.le_congr (SignedRatio.equiv_symm sharp.lowerAttained) (SignedRatio.equiv_refl _)).mp
          (sharp.bounds model fits).1)))
  else .possible sharp.lowerModel sharp.lowerFits (Nat.eq_zero_of_not_pos minimum)

inductive ConditionalResult (spec : Specification fine coarse) (evidence event : EventQuery fine) where
  | invalid (reason : ¬ spec.Valid)
  | incompatible (valid : spec.Valid) (excluded : ¬ ∃ model : ExactModel fine, spec.Fits model)
  | undefined (valid : spec.Valid) (model : ExactModel fine) (fits : spec.Fits model)
      (allNull : ∀ candidate, spec.Fits candidate → (evidence.value candidate).num = 0)
  | supported (valid : spec.Valid) (sharp : spec.ConditionalBounds evidence event)
      (nullEvidence : spec.NullEvidence evidence)

/-- Interpret the sharp evidence range before invoking conditional
optimization. A reduced solver can supply bounds and a range program
already transported back to the complete fine table problem. -/
def conditionalResultOfBounds (spec : Specification fine coarse) (valid : spec.Valid)
    (evidence event : EventQuery fine)
    (tableBounds : spec.problem.SharpBounds (eventResponse evidence.onTable))
    (computeRange : spec.problem.ConditionalLaw evidence.onTable →
      spec.problem.ConditionalRange evidence.onTable event.onTable) :
    spec.ConditionalResult evidence event :=
  let sharp := spec.queryBoundsOfMoment evidence tableBounds
  if positive : tableBounds.upperLaw.distro.record.EventPositive evidence.onTable then
    let reference : spec.problem.ConditionalLaw evidence.onTable :=
      ⟨tableBounds.upperLaw.distro, spec.table_support _, tableBounds.upperLaw.moments, positive⟩
    .supported valid
      (spec.conditionalBoundsOfRange evidence event (computeRange reference))
      (nullEvidenceOfBounds sharp)
  else
    .undefined valid sharp.upperModel sharp.upperFits (by
      intro model fits
      apply Nat.eq_zero_of_not_pos
      intro candidatePositive
      apply positive
      apply (QProb.equiv_num_pos_iff (evidence.value_of_responseLaw _)).mp
      exact positive_of_le candidatePositive ((SignedRatio.toSignedRatio_le_iff _ _).mp
        ((SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm sharp.upperAttained)).mp
          (sharp.bounds model fits).2)))

/-- Only a positive attained upper evidence mass starts fractional
optimization. A null maximum supplies a fitted witness and excludes positive
denominators throughout the class. -/
def solveConditional (spec : Specification fine coarse) (evidence event : EventQuery fine) :
    spec.ConditionalResult evidence event :=
  if valid : spec.Valid then
    match spec.problem.solveEventBounds evidence.onTable with
    | .infeasible certificate => .incompatible valid (spec.infeasible_not_exists certificate)
    | .bounded tableBounds => spec.conditionalResultOfBounds valid evidence event tableBounds
        (spec.problem.conditionalRange evidence.onTable event.onTable)
  else .invalid valid

end Specification
end Thesis.Causality.CausalAbstractionInverse
