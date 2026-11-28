import Thesis.Causality.CausalAbstractionProtocol
import Thesis.Causality.Counterfactual
import Thesis.Causality.SharedResponseModel
import Thesis.Probability.Distros.PartialMomentBounds

/-!
# Sharp fine-level queries from coarse experimental laws

The fine signature, its allowed parents, and the abstraction protocol are
fixed. The unknown is a law on the complete carrier of fine response tables.
A measurement is an exact joint law at a coarse setting. Every admitted
representative of that setting is constrained, and repeated measurements
remain independent equality obligations. Validation requires measurements
at every required setting, including observation.

The optimization ranges over all finite rational SCMs of the fine
signature. A single shared source realizes each endpoint; every model in
the class induces a response law, with no bound on its source alphabet or
denominator. Graphical restrictions on shared latent dependence would
change this model class.
-/

namespace Thesis.Causality.CausalAbstractionInverse

open Probability Probability.Distros
open CausalAbstractionSynthesis (Protocol interventionDecidableEq interventions interventions_complete)
open SharedResponse (Table)

variable {fine coarse : ObservedSignature.{0}}

/-- A supplied experimental law, rather than empirical counts or a model
that must generate all the measurements. -/
structure Measurement (coarse : ObservedSignature.{0}) where
  action : HardIntervention coarse
  law : FiniteProbRecord coarse.Assignment

structure Specification (fine coarse : ObservedSignature.{0}) extends Protocol fine coarse where
  measurements : List (Measurement coarse)

/-- Both kinds of query are evaluated on one response table per unit. In a
multiworld formula all intervention atoms refer to that same table. -/
inductive EventQuery (fine : ObservedSignature.{0}) where
  | intervention (action : HardIntervention fine) (event : Event fine.Assignment)
  | counterfactual (event : CounterfactualEvent fine)
  | conj (left right : EventQuery fine)

namespace EventQuery

private def tableHolds (table : Table fine) : CounterfactualEvent fine → Bool
  | .truth => true
  | .falsity => false
  | .atom atom => decide (SharedResponse.eval fine atom.action table atom.node = atom.value)
  | .conj left right => tableHolds table left && tableHolds table right
  | .disj left right => tableHolds table left || tableHolds table right
  | .neg event => !(tableHolds table event)

private theorem holds_eq_tableHolds (event : CounterfactualEvent fine)
    (model : ExactModel fine) (unit : model.latent.Assignment) (table : Table fine)
    (agrees : ∀ action, model.evalUnder action unit = SharedResponse.eval fine action table) :
    event.holds model unit = tableHolds table event := by
  induction event with
  | truth => rfl
  | falsity => rfl
  | atom atom => simp only [CounterfactualEvent.holds, CounterfactualAtom.holds, tableHolds, agrees]
  | conj left right leftIH rightIH => simp only [CounterfactualEvent.holds, tableHolds, leftIH, rightIH]
  | disj left right leftIH rightIH => simp only [CounterfactualEvent.holds, tableHolds, leftIH, rightIH]
  | neg inner ih => simp only [CounterfactualEvent.holds, tableHolds, ih]

def onTable : EventQuery fine → Event (Table fine)
  | .intervention a event => fun table => event (SharedResponse.eval fine a.value table)
  | .counterfactual event => fun table => tableHolds table event
  | .conj left right => fun table => left.onTable table && right.onTable table

def holds (query : EventQuery fine) (model : ExactModel fine) : Event model.latent.Assignment :=
  match query with
  | .intervention a event => fun unit => event (model.evalUnder a.value unit)
  | .counterfactual event => event.holds model
  | .conj left right => fun unit => left.holds model unit && right.holds model unit

/-- Native semantics at an actual model, independent of the solver. -/
def value (query : EventQuery fine) (model : ExactModel fine) : QProb :=
  match query with
  | .intervention a event => model.interventionalValue a.value event
  | .counterfactual event => model.prior.probVal (event.holds model)
  | .conj left right => model.prior.probVal ((conj left right).holds model)

theorem value_eq_probVal (query : EventQuery fine) (model : ExactModel fine) :
    QProb.Equiv (query.value model) (model.prior.probVal (query.holds model)) := by
  cases query with
  | intervention a event => exact model.interventionalValue_eq a.value event
  | counterfactual _ => exact QProb.equiv_refl _
  | conj _ _ => exact QProb.equiv_refl _

/-- Pointwise execution suffices for an entire Boolean multiworld formula. -/
theorem holds_eq_onTable (query : EventQuery fine) (model : ExactModel fine)
    (unit : model.latent.Assignment) (table : Table fine)
    (agrees : ∀ action, model.evalUnder action unit = SharedResponse.eval fine action table) :
    query.holds model unit = query.onTable table := by
  induction query with
  | intervention a event => exact congrArg event (agrees a.value)
  | counterfactual event => exact holds_eq_tableHolds event model unit table agrees
  | conj left right leftIH rightIH => simp only [holds, onTable, leftIH, rightIH]

theorem holds_responseOf (query : EventQuery fine) (model : ExactModel fine)
    (unit : model.latent.Assignment) :
    query.holds model unit = query.onTable (SharedResponse.responseOf fine model unit) :=
  query.holds_eq_onTable model unit _ (fun action =>
    (SharedResponse.eval_responseOf fine model unit action).symm)

theorem holds_model (query : EventQuery fine) (law : FiniteProbRecord (Table fine))
    (unit : (SharedResponse.latent fine).Assignment) :
    query.holds (SharedResponse.model fine law) unit = query.onTable (unit (SharedResponse.root fine)) :=
  query.holds_eq_onTable (SharedResponse.model fine law) unit _ (fun action =>
    SharedResponse.model_eval fine law action unit)

theorem value_of_responseLaw (query : EventQuery fine) (law : FiniteProbRecord (Table fine)) :
    QProb.Equiv (query.value (SharedResponse.model fine law)) (law.probVal query.onTable) :=
  QProb.equiv_trans (query.value_eq_probVal (SharedResponse.model fine law))
    (QProb.equiv_trans ((SharedResponse.model fine law).prior.probVal_congr (query.holds _)
      (fun unit => query.onTable (unit (SharedResponse.root fine))) (query.holds_model law))
      (law.map_probVal (fun table _ => table)
        (fun unit : (SharedResponse.latent fine).Assignment => query.onTable (unit (SharedResponse.root fine)))))

theorem responseLaw_value (query : EventQuery fine) (model : ExactModel fine) :
    QProb.Equiv ((SharedResponse.lawOf fine model).probVal query.onTable) (query.value model) :=
  QProb.equiv_trans (model.prior.map_probVal (SharedResponse.responseOf fine model) query.onTable)
    (QProb.equiv_trans (model.prior.probVal_congr
      (fun unit => query.onTable (SharedResponse.responseOf fine model unit)) (query.holds model)
      (fun unit => (query.holds_responseOf model unit).symm))
      (QProb.equiv_symm (query.value_eq_probVal model)))

end EventQuery

namespace Specification

/-- Every measured law is compared against every representative of its
setting. An unmeasured optional setting contributes no numerical constraint. -/
def comparisons (spec : Specification fine coarse) :
    List (HardIntervention fine × Measurement coarse) :=
  (interventions fine).flatMap fun a =>
    (spec.measurements.filter fun measured => decide (spec.omega a = some measured.action)).map
      (fun measured => (a, measured))

theorem comparison_iff (spec : Specification fine coarse) (a : HardIntervention fine)
    (measured : Measurement coarse) :
    (a, measured) ∈ spec.comparisons ↔
      measured ∈ spec.measurements ∧ spec.omega a = some measured.action := by
  constructor
  · intro member
    obtain ⟨source, _, inMap⟩ := List.mem_flatMap.mp member
    obtain ⟨datum, filtered, same⟩ := List.mem_map.mp inMap
    cases same
    simpa using (List.mem_filter.mp filtered)
  · rintro ⟨listed, mapped⟩
    exact List.mem_flatMap.mpr ⟨a, interventions_complete fine a,
      List.mem_map.mpr ⟨measured, List.mem_filter.mpr ⟨listed, decide_eq_true mapped⟩, rfl⟩⟩

/-- Protocol validity and data availability are checked before solving
the response problem. Extra measurements outside the image have no fine
representative and are rejected. -/
def Valid (spec : Specification fine coarse) : Prop :=
  spec.toProtocol.Valid ∧
    (∀ action ∈ spec.required, ∃ measured ∈ spec.measurements, measured.action = action) ∧
    (∀ measured ∈ spec.measurements, ∃ pair ∈ spec.toProtocol.comparisons,
      pair.2 = measured.action)

instance (spec : Specification fine coarse) : Decidable spec.Valid := by
  unfold Valid
  infer_instance

/-- Each required coarse experiment has both a measured law and a fine
representative that actually enters the linear problem. -/
theorem covered (spec : Specification fine coarse) (valid : spec.Valid)
    (action : HardIntervention coarse) (required : action ∈ spec.required) :
    ∃ a measured, (a, measured) ∈ spec.comparisons ∧ measured.action = action := by
  obtain ⟨a, mapped⟩ := spec.toProtocol.covered valid.1 action required
  obtain ⟨measured, listed, tag⟩ := valid.2.1 action required
  exact ⟨a, measured, (spec.comparison_iff a measured).mpr ⟨listed, tag ▸ mapped⟩, tag⟩

def readout (spec : Specification fine coarse) (a : HardIntervention fine)
    (table : Table fine) : coarse.Assignment :=
  spec.aggregation.assignmentMap (SharedResponse.eval fine a.value table)

/-- Compatibility concerns every event at every compared experiment. -/
def Fits (spec : Specification fine coarse) (model : ExactModel fine) : Prop :=
  ∀ pair ∈ spec.comparisons, ∀ event : Event coarse.Assignment,
    QProb.Equiv (model.interventionalValue pair.1.value
      (fun state => event (spec.aggregation.assignmentMap state))) (pair.2.law.probVal event)

def ResponseFits (spec : Specification fine coarse) (law : FiniteProbRecord (Table fine)) : Prop :=
  ∀ pair ∈ spec.comparisons, ∀ event : Event coarse.Assignment,
    QProb.Equiv (law.probVal (fun table => event (spec.readout pair.1 table)))
      (pair.2.law.probVal event)

def problem (spec : Specification fine coarse) : PartialMomentProblem (Table fine) where
  cells := SharedResponse.enumeration fine
  default := SharedResponse.defaultTable fine
  nonempty := SharedResponse.enumeration_nonempty fine
  distinct := SharedResponse.enumeration_nodup fine
  intervals := spec.comparisons.flatMap fun pair => coarse.assignmentEnumeration.map
    (MomentInterval.exactPushforward (spec.readout pair.1) pair.2.law)

theorem moments_iff_responseFits (spec : Specification fine coarse) (law : Distro (Table fine)) :
    (∀ row ∈ spec.problem.intervals, row.LawHolds law) ↔ spec.ResponseFits law.record := by
  have byExperiment (pair : HardIntervention fine × Measurement coarse) :=
    MomentInterval.exactPushforward_iff law (spec.readout pair.1) pair.2.law
      coarse.assignmentEnumeration coarse.assignmentEnumeration_nodup
      coarse.assignmentEnumeration_complete
  constructor
  · intro moments pair listed
    exact (byExperiment pair).mp (fun row member =>
      moments row (List.mem_flatMap.mpr ⟨pair, listed, member⟩))
  · intro fits row member
    obtain ⟨pair, listed, rowMember⟩ := List.mem_flatMap.mp member
    exact (byExperiment pair).mpr (fits pair listed) row rowMember

theorem fits_of_responseFits (spec : Specification fine coarse) (law : FiniteProbRecord (Table fine))
    (fits : spec.ResponseFits law) : spec.Fits (SharedResponse.model fine law) := by
  intro pair listed event
  exact QProb.equiv_trans (SharedResponse.model_interventionalValue fine law pair.1.value
    (fun state => event (spec.aggregation.assignmentMap state)))
    (fits pair listed event)

theorem responseFits_of_fits (spec : Specification fine coarse) (model : ExactModel fine)
    (fits : spec.Fits model) : spec.ResponseFits (SharedResponse.lawOf fine model) := by
  intro pair listed event
  exact QProb.equiv_trans (SharedResponse.lawOf_interventionalValue fine model pair.1.value
      (fun state => event (spec.aggregation.assignmentMap state)))
    (fits pair listed event)

/-- An exact linear witness supplies an actual fine SCM. -/
def fittedModel (spec : Specification fine coarse) (law : spec.problem.CompatibleLaw) :
    ExactModel fine :=
  SharedResponse.model fine law.distro.record

theorem fittedModel_fits (spec : Specification fine coarse) (law : spec.problem.CompatibleLaw) :
    spec.Fits (spec.fittedModel law) :=
  spec.fits_of_responseFits law.distro.record
    ((spec.moments_iff_responseFits law.distro).mp law.moments)

theorem table_support (spec : Specification fine coarse) (law : Distro (Table fine)) :
    law.AlmostSurely (fun table => table ∈ spec.problem.cells) := by
  intro atom _ _
  exact SharedResponse.enumeration_complete fine atom.1

theorem infeasible_not_exists (spec : Specification fine coarse)
    (certificate : RationalLinear.Infeasibility spec.problem.cells.length spec.problem.rows) :
    ¬ ∃ model : ExactModel fine, spec.Fits model := by
  rintro ⟨model, fits⟩
  let law : Distro (Table fine) := ⟨SharedResponse.lawOf fine model⟩
  exact spec.problem.refutation_not_realizable certificate
    ⟨law, spec.table_support law, (spec.moments_iff_responseFits law).mpr
      (spec.responseFits_of_fits model fits)⟩

/-- Sharp bounds in the original fine model class. The endpoint models
are both compatible with the coarse laws and attain the reported values. -/
structure QueryBounds (spec : Specification fine coarse) (query : EventQuery fine) where
  lower : SignedRatio
  upper : SignedRatio
  lowerModel : ExactModel fine
  upperModel : ExactModel fine
  lowerFits : spec.Fits lowerModel
  upperFits : spec.Fits upperModel
  lowerAttained : SignedRatio.Equiv (query.value lowerModel).toSignedRatio lower
  upperAttained : SignedRatio.Equiv (query.value upperModel).toSignedRatio upper
  bounds : ∀ model, spec.Fits model →
    SignedRatio.LE lower (query.value model).toSignedRatio ∧
    SignedRatio.LE (query.value model).toSignedRatio upper

def queryBoundsOfMoment (spec : Specification fine coarse) (query : EventQuery fine)
    (sharp : spec.problem.SharpBounds (eventResponse query.onTable)) :
    spec.QueryBounds query where
  lower := sharp.lower
  upper := sharp.upper
  lowerModel := spec.fittedModel sharp.lowerLaw
  upperModel := spec.fittedModel sharp.upperLaw
  lowerFits := spec.fittedModel_fits sharp.lowerLaw
  upperFits := spec.fittedModel_fits sharp.upperLaw
  lowerAttained := SignedRatio.equiv_trans
    (QProb.toSignedRatio_congr (query.value_of_responseLaw _)) sharp.event_lower_attained
  upperAttained := SignedRatio.equiv_trans
    (QProb.toSignedRatio_congr (query.value_of_responseLaw _)) sharp.event_upper_attained
  bounds := by
    intro model fits
    let law : Distro (Table fine) := ⟨SharedResponse.lawOf fine model⟩
    have bounded := sharp.event_bounds law (spec.table_support law)
      ((spec.moments_iff_responseFits law).mpr (spec.responseFits_of_fits model fits))
    have preserved := QProb.toSignedRatio_congr (query.responseLaw_value model)
    exact ⟨(SignedRatio.le_congr (SignedRatio.equiv_refl _) preserved).mp bounded.1,
      (SignedRatio.le_congr preserved (SignedRatio.equiv_refl _)).mp bounded.2⟩

/-- Coincident endpoints give a uniform value over the nonempty class. -/
theorem QueryBounds.point {spec : Specification fine coarse} {query : EventQuery fine}
    (sharp : spec.QueryBounds query) (same : SignedRatio.Equiv sharp.lower sharp.upper)
    (model : ExactModel fine) (fits : spec.Fits model) :
    SignedRatio.Equiv (query.value model).toSignedRatio sharp.lower := by
  have bounded := sharp.bounds model fits
  exact SignedRatio.equiv_of_le_of_le
    ((SignedRatio.le_congr (SignedRatio.equiv_refl _) (SignedRatio.equiv_symm same)).mp
      bounded.2) bounded.1

inductive QueryResult (spec : Specification fine coarse) (query : EventQuery fine) where
  | invalid (reason : ¬ spec.Valid)
  | incompatible (valid : spec.Valid) (excluded : ¬ ∃ model : ExactModel fine, spec.Fits model)
  | point (valid : spec.Valid) (sharp : spec.QueryBounds query)
      (same : SignedRatio.Equiv sharp.lower sharp.upper)
  | interval (valid : spec.Valid) (sharp : spec.QueryBounds query)
      (different : ¬ SignedRatio.Equiv sharp.lower sharp.upper)

/-- Validate the experiment interface, then solve the fine query exactly. -/
def solveQuery (spec : Specification fine coarse) (query : EventQuery fine) : spec.QueryResult query :=
  if valid : spec.Valid then
    match spec.problem.solveEventBounds query.onTable with
    | .infeasible certificate => .incompatible valid (spec.infeasible_not_exists certificate)
    | .bounded bounds =>
        let sharp := spec.queryBoundsOfMoment query bounds
        if same : SignedRatio.Equiv sharp.lower sharp.upper then .point valid sharp same
        else .interval valid sharp same
  else .invalid valid

abbrev SharpBounds (spec : Specification fine coarse) (a : HardIntervention fine)
    (event : Event fine.Assignment) :=
  spec.QueryBounds (.intervention a event)

abbrev Result (spec : Specification fine coarse) (a : HardIntervention fine)
    (event : Event fine.Assignment) :=
  spec.QueryResult (.intervention a event)

/-- Unconditional interventional queries use the same solver, with a
one-world event as their response-table objective. -/
def solve (spec : Specification fine coarse) (a : HardIntervention fine)
    (event : Event fine.Assignment) : spec.Result a event :=
  spec.solveQuery (.intervention a event)

end Specification
end Thesis.Causality.CausalAbstractionInverse
