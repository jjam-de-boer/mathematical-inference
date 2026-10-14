import Thesis.Causality.BinaryInstrumentalTransportation
import Thesis.Probability.FourLabelTransportationAggregation
import Thesis.Probability.FiniteRecordOverlap

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability
open FourLabelTransportation

/-!
# Unit-level exposure of an IV intervention outcome

If either instrument arm receives the requested treatment and exhibits the
requested outcome, that unit's corresponding potential outcome has that
value.  The two arm events can overlap.  Their intersection is the same-
treatment/same-outcome cell, represented by an *off*-diagonal edge after
flipping the column outcome.  It must not be confused with a forbidden cell.

The exact natural-mass inequality keeps the overlap explicit.  It applies
to every supplied response record, including arbitrary denominators, repeated
labels, and zeros.  Combining it with a universal cell maximum gives causal
risk bounds; no observational adjustment formula or monotonicity assumption
is inserted into this unit-level statement.
-/

def outcomeEvent (action outcome : Bool) : Event Profile :=
  fun profile => decide (outcomeAt profile action = outcome)

theorem outcomeEvent_true (profile : Profile) (action : Bool) :
    outcomeEvent action true profile = outcomeAt profile action := by
  unfold outcomeEvent
  cases outcomeAt profile action <;> rfl

theorem outcomeEvent_false (profile : Profile) (action : Bool) :
    outcomeEvent action false profile = !(outcomeEvent action true profile) := by
  unfold outcomeEvent
  cases outcomeAt profile action <;> rfl

theorem outcomeEvent_partition (responses : FiniteProbRecord Profile) (action : Bool) :
    FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) +
      FiniteProbRecord.eventMass responses.atoms (outcomeEvent action false) = responses.den := by
  have complement : (fun profile => !(outcomeEvent action true profile)) = outcomeEvent action false :=
    funext (fun profile => (outcomeEvent_false profile action).symm)
  have partition := FiniteProbRecord.eventMass_add_complement responses.atoms (outcomeEvent action true)
  rw [complement] at partition
  exact partition.trans responses.total_mass

def riskEdge (action outcome : Bool) : Fin 4 × Fin 4 :=
  (encodeCategory action outcome, encodeCategory action (!outcome))

theorem riskEdge_different : forall action outcome : Bool,
    (riskEdge action outcome).1 ≠ (riskEdge action outcome).2 := by decide +kernel

def responseEdges (responses : FiniteProbRecord Profile) : FiniteProbRecord (Fin 4 × Fin 4) :=
  (responseCoupling responses).map edgeOfPair

theorem responseEdges_row_mass (responses : FiniteProbRecord Profile) (row : Fin 4) :
    aggregateRows (responseEdges responses) row =
      FiniteProbRecord.eventMass responses.atoms (responseCell false (decodeCategory row).1 (decodeCategory row).2) := by
  simp only [aggregateRows, responseEdges, responseCoupling, FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels]
  apply FiniteProbRecord.eventMass_congr
  intro profile
  exact (edgeOfPair_row_match (responsePair profile) row).trans
    (couplingCell_responsePair false (decodeCategory row).1 (decodeCategory row).2 profile)

theorem responseEdges_column_mass (responses : FiniteProbRecord Profile) (column : Fin 4) :
    aggregateColumns (responseEdges responses) column =
      FiniteProbRecord.eventMass responses.atoms (responseCell true (decodeCategory column).1 (!(decodeCategory column).2)) := by
  simp only [aggregateColumns, responseEdges, responseCoupling, FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels]
  apply FiniteProbRecord.eventMass_congr
  intro profile
  exact (edgeOfPair_column_match (responsePair profile) column).trans
    (couplingCell_responsePair true (decodeCategory column).1 (!(decodeCategory column).2) profile)

private theorem profile_edge_inter (profile : Profile) (action outcome : Bool) :
    FiniteProbRecord.singletonEvent (riskEdge action outcome) (edgeOfPair (responsePair profile)) =
      inter (responseCell false action outcome) (responseCell true action outcome) profile := by
  cases firstTreatment : treatmentAt profile false <;> cases secondTreatment : treatmentAt profile true <;>
    cases controlOutcome : outcomeAt profile false <;> cases treatedOutcome : outcomeAt profile true <;>
    cases action <;> cases outcome <;>
    simp [FiniteProbRecord.singletonEvent, riskEdge, edgeOfPair, responsePair, encodeCategory,
      responseCell, inter, firstTreatment, secondTreatment, controlOutcome, treatedOutcome]

/-- Actual overlap mass of the two instrument arms, with its original
response denominator.  This is not an assumed independence of the events. -/
theorem responseEdges_inter_mass (responses : FiniteProbRecord Profile) (action outcome : Bool) :
    aggregateCells (responseEdges responses) (riskEdge action outcome).1 (riskEdge action outcome).2 =
      FiniteProbRecord.eventMass responses.atoms (inter (responseCell false action outcome) (responseCell true action outcome)) := by
  simp only [aggregateCells, responseEdges, responseCoupling, FiniteProbRecord.map, FiniteProbRecord.eventMass_map_labels]
  exact FiniteProbRecord.eventMass_congr responses.atoms _ _ (fun profile => profile_edge_inter profile action outcome)

/-- The sum of both exposed arm masses is bounded by the true intervention
outcome mass plus their true overlap.  Natural subtraction is unnecessary,
so null events and zero-weight profiles need no special totalization. -/
theorem response_outcome_exposure (responses : FiniteProbRecord Profile) (action outcome : Bool) :
    aggregateRows (responseEdges responses) (riskEdge action outcome).1 +
        aggregateColumns (responseEdges responses) (riskEdge action outcome).2 ≤
      FiniteProbRecord.eventMass responses.atoms (outcomeEvent action outcome) +
        aggregateCells (responseEdges responses) (riskEdge action outcome).1 (riskEdge action outcome).2 := by
  rw [responseEdges_row_mass, responseEdges_column_mass, responseEdges_inter_mass]
  simp only [riskEdge, decode_encodeCategory, Bool.not_not]
  exact FiniteProbRecord.eventMass_exposure responses.atoms (responseCell false action outcome)
    (responseCell true action outcome) (outcomeEvent action outcome)
    (fun _ selected => (Bool.and_eq_true_iff.mp selected).2)
    (fun _ selected => (Bool.and_eq_true_iff.mp selected).2)

end BinaryInstrumental
end Causality
end Thesis
