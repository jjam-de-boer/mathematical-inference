import Thesis.CausalTransport.BinaryInstrumental.RiskBounds

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability
open FourLabelTransportation

/-!
# One native model attaining any chosen pair of IV risk endpoints

The two Boolean choices request a lower or upper risk under control and
treatment.  For a lower risk, maximize overlap of observed successes and
set an unobserved response to false.  For an upper risk, maximize overlap
of observed failures and set the unobserved response to true.  If the two
choices differ, the fill rule depends on which treatment was factual.

The two requested overlap edges always have distinct rows and columns and
cover all four labels.  The joint transportation constructor therefore
attains both maxima in one table.  Its explicit profile fill preserves the
whole observed law, and exact overlap accounting gives both requested
intervention-risk values in one genuine native model on the original DAG.

This theorem permits zeros in individual arm cells and capacities.  It
uses normalized arm margins and their checked whole-law equations; the
computed-margin specialization and null-instrument branch are assembled
separately.  It never subtracts endpoints witnessed by unrelated models.
-/

def endpointUpper (controlUpper treatedUpper action : Bool) : Bool :=
  if action then treatedUpper else controlUpper

/-- Only a treatment absent from both arms needs filling.  Its upper/lower
choice is the one opposite to the factual treatment stored in the pair. -/
def endpointFill (controlUpper treatedUpper : Bool) (pair : ResponsePair) : Bool :=
  if pair.1.1 then controlUpper else treatedUpper

def endpointEdge (controlUpper treatedUpper action : Bool) : Fin 4 × Fin 4 :=
  riskEdge action (!(endpointUpper controlUpper treatedUpper action))

theorem endpoint_edges_complementary (controlUpper treatedUpper : Bool) :
    ComplementaryEdges (endpointEdge controlUpper treatedUpper false) (endpointEdge controlUpper treatedUpper true) := by
  cases controlUpper <;> cases treatedUpper <;>
    refine ⟨by decide +kernel, by decide +kernel, ?_⟩ <;> decide +kernel

private theorem edge_filled_outcome_union : forall row column : Fin 4, forall controlUpper treatedUpper action : Bool,
    offDiagonal (row, column) = true →
      outcomeEvent action (!(endpointUpper controlUpper treatedUpper action))
          (profileOfPair (pairOfEdge (row, column)) (endpointFill controlUpper treatedUpper (pairOfEdge (row, column)))) =
        union (rowEvent (endpointEdge controlUpper treatedUpper action).1)
          (columnEvent (endpointEdge controlUpper treatedUpper action).2) (row, column) := by
  decide +kernel

private theorem row_column_inter (edge : Fin 4 × Fin 4) :
    inter (rowEvent edge.1) (columnEvent edge.2) = FiniteProbRecord.singletonEvent edge := by
  funext pair
  apply Bool.eq_iff_iff.mpr
  simp only [inter, rowEvent, columnEvent, FiniteProbRecord.singletonEvent, Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨atRow, atColumn⟩
    exact Prod.ext atRow atColumn
  · intro same
    exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

def endpointResponses (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (table : Transportation rows columns) (controlUpper treatedUpper : Bool) :
    FiniteProbRecord Profile :=
  transportationResponses total positive rows columns margins table (endpointFill controlUpper treatedUpper)

/-- Once the missing outcome is filled in the chosen direction, exposure
is an equality, not merely the universal lower inequality.  Zero-weight
forbidden cells are handled by probability-one support of the real record. -/
theorem endpoint_outcome_mass (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (table : Transportation rows columns)
    (controlUpper treatedUpper action : Bool) :
    FiniteProbRecord.eventMass (endpointResponses total positive rows columns margins table controlUpper treatedUpper).atoms
        (outcomeEvent action (!(endpointUpper controlUpper treatedUpper action))) +
      table.cells (endpointEdge controlUpper treatedUpper action).1 (endpointEdge controlUpper treatedUpper action).2 =
        rows (endpointEdge controlUpper treatedUpper action).1 + columns (endpointEdge controlUpper treatedUpper action).2 := by
  let base := record total positive rows columns margins table
  let responses := endpointResponses total positive rows columns margins table controlUpper treatedUpper
  let edge := endpointEdge controlUpper treatedUpper action
  let target := outcomeEvent action (!(endpointUpper controlUpper treatedUpper action))
  let exposed := union (rowEvent edge.1) (columnEvent edge.2)
  have mapped : QProb.Equiv (responses.probVal target)
      (base.probVal (fun item => target (profileOfPair (pairOfEdge item) (endpointFill controlUpper treatedUpper (pairOfEdge item))))) :=
    QProb.equiv_trans
      ((transportationCoupling total positive rows columns margins table).map_probVal
        (fun pair => profileOfPair pair (endpointFill controlUpper treatedUpper pair)) target)
      (base.map_probVal pairOfEdge (fun pair => target (profileOfPair pair (endpointFill controlUpper treatedUpper pair))))
  have same : QProb.Equiv (responses.probVal target) (base.probVal exposed) :=
    QProb.equiv_trans mapped
      (base.probVal_congr_on_probability_one offDiagonal _ _
        (record_offDiagonal total positive rows columns margins table)
        (fun item allowed => edge_filled_outcome_union item.1 item.2 controlUpper treatedUpper action allowed))
  have mass : FiniteProbRecord.eventMass responses.atoms target = FiniteProbRecord.eventMass base.atoms exposed := by
    change FiniteProbRecord.eventMass responses.atoms target * total = FiniteProbRecord.eventMass base.atoms exposed * total at same
    exact Nat.eq_of_mul_eq_mul_right positive same
  have overlap := FiniteProbRecord.eventMass_union_add_inter base.atoms (rowEvent edge.1) (columnEvent edge.2)
  rw [row_column_inter] at overlap
  change FiniteProbRecord.eventMass (tableAtoms table.cells) exposed +
    FiniteProbRecord.eventMass (tableAtoms table.cells) (FiniteProbRecord.singletonEvent edge) =
      FiniteProbRecord.eventMass (tableAtoms table.cells) (rowEvent edge.1) +
      FiniteProbRecord.eventMass (tableAtoms table.cells) (columnEvent edge.2) at overlap
  rw [tableAtoms_cell] at overlap
  change FiniteProbRecord.eventMass (tableAtoms table.cells) exposed + table.cells edge.1 edge.2 =
    FiniteProbRecord.eventMass (tableAtoms table.cells) (fun pair => decide (pair.1 = edge.1)) +
      FiniteProbRecord.eventMass (tableAtoms table.cells) (fun pair => decide (pair.2 = edge.2)) at overlap
  rw [tableAtoms_row, tableAtoms_column, table.row_sum, table.column_sum] at overlap
  change FiniteProbRecord.eventMass responses.atoms target + table.cells edge.1 edge.2 = rows edge.1 + columns edge.2
  rw [mass]
  exact overlap

/-- The outcome whose overlap was maximized has exactly its lower mass.
For a requested upper success risk this is the *failure* mass, which is
also the component needed by the signed-effect score.  This raw equality
keeps the constructor's common denominator available for joint objectives. -/
theorem endpoint_selected_outcome_mass (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (table : Transportation rows columns)
    (controlUpper treatedUpper action : Bool)
    (attained : table.cells (endpointEdge controlUpper treatedUpper action).1 (endpointEdge controlUpper treatedUpper action).2 =
      edgeCapacity total rows columns (endpointEdge controlUpper treatedUpper action)) :
    FiniteProbRecord.eventMass (endpointResponses total positive rows columns margins table controlUpper treatedUpper).atoms
        (outcomeEvent action (!(endpointUpper controlUpper treatedUpper action))) =
      outcomeLowerMass total rows columns action (!(endpointUpper controlUpper treatedUpper action)) := by
  have exposed := endpoint_outcome_mass total positive rows columns margins table controlUpper treatedUpper action
  rw [attained] at exposed
  change _ + edgeCapacity total rows columns (riskEdge action (!(endpointUpper controlUpper treatedUpper action))) =
    rows (riskEdge action (!(endpointUpper controlUpper treatedUpper action))).1 +
      columns (riskEdge action (!(endpointUpper controlUpper treatedUpper action))).2 at exposed
  clear attained
  unfold outcomeLowerMass
  omega

def selectedRisk (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (controlUpper treatedUpper action : Bool) : QProb :=
  if endpointUpper controlUpper treatedUpper action then riskUpper total positive rows columns action
  else riskLower total positive rows columns action

/-- A table attaining the selected overlap maximum yields precisely the
requested lower or upper success risk, with the original common denominator. -/
theorem endpoint_response_risk (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (table : Transportation rows columns)
    (controlUpper treatedUpper action : Bool)
    (attained : table.cells (endpointEdge controlUpper treatedUpper action).1 (endpointEdge controlUpper treatedUpper action).2 =
      edgeCapacity total rows columns (endpointEdge controlUpper treatedUpper action)) :
    QProb.Equiv ((effectRecord (endpointResponses total positive rows columns margins table controlUpper treatedUpper) action).probVal id)
      (selectedRisk total positive rows columns controlUpper treatedUpper action) := by
  let responses := endpointResponses total positive rows columns margins table controlUpper treatedUpper
  have exposed := endpoint_outcome_mass total positive rows columns margins table controlUpper treatedUpper action
  rw [attained] at exposed
  have semantics : QProb.Equiv ((effectRecord responses action).probVal id) (responses.probVal (outcomeEvent action true)) :=
    QProb.equiv_trans (effectRecord_probVal responses action)
      (responses.probVal_congr _ _ (fun profile => (outcomeEvent_true profile action).symm))
  apply QProb.equiv_trans semantics
  cases chosen : endpointUpper controlUpper treatedUpper action with
  | false =>
      simp only [endpointEdge, chosen, Bool.not_false] at exposed
      have exactMass : FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) = outcomeLowerMass total rows columns action true := by
        change FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) +
          edgeCapacity total rows columns (riskEdge action true) = rows (riskEdge action true).1 + columns (riskEdge action true).2 at exposed
        unfold outcomeLowerMass
        clear attained
        omega
      simp only [selectedRisk, chosen, Bool.false_eq_true, if_false]
      change QProb.Equiv (responses.probVal (outcomeEvent action true)) (riskLower total positive rows columns action)
      change FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) * total =
        outcomeLowerMass total rows columns action true * total
      rw [exactMass]
  | true =>
      simp only [endpointEdge, chosen, Bool.not_true] at exposed
      have failure : FiniteProbRecord.eventMass responses.atoms (outcomeEvent action false) = outcomeLowerMass total rows columns action false := by
        change FiniteProbRecord.eventMass responses.atoms (outcomeEvent action false) +
          edgeCapacity total rows columns (riskEdge action false) = rows (riskEdge action false).1 + columns (riskEdge action false).2 at exposed
        unfold outcomeLowerMass
        clear attained
        omega
      have partition := outcomeEvent_partition responses action
      rw [failure] at partition
      have exactMass : FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) = total - outcomeLowerMass total rows columns action false := by
        change _ + _ = total at partition
        omega
      simp only [selectedRisk, chosen, if_true]
      change QProb.Equiv (responses.probVal (outcomeEvent action true)) (riskUpper total positive rows columns action)
      change FiniteProbRecord.eventMass responses.atoms (outcomeEvent action true) * total =
        (total - outcomeLowerMass total rows columns action false) * total
      rw [exactMass]

def endpointTable (total : Nat) (rows columns : Masses) (margins : Margins total rows columns)
    (controlUpper treatedUpper : Bool) : Transportation rows columns :=
  maximizeComplementary total rows columns margins (endpointEdge controlUpper treatedUpper false)
    (endpointEdge controlUpper treatedUpper true) (riskEdge_different false _) (riskEdge_different true _)
    (endpoint_edges_complementary controlUpper treatedUpper)

theorem endpointTable_attains (total : Nat) (rows columns : Masses) (margins : Margins total rows columns)
    (controlUpper treatedUpper action : Bool) :
    (endpointTable total rows columns margins controlUpper treatedUpper).cells
      (endpointEdge controlUpper treatedUpper action).1 (endpointEdge controlUpper treatedUpper action).2 =
        edgeCapacity total rows columns (endpointEdge controlUpper treatedUpper action) := by
  have attained := maximizeComplementary_attains total rows columns margins
    (endpointEdge controlUpper treatedUpper false) (endpointEdge controlUpper treatedUpper true)
    (riskEdge_different false _) (riskEdge_different true _) (endpoint_edges_complementary controlUpper treatedUpper)
  cases action
  · exact attained.1
  · exact attained.2

/-- Every chosen pair of risk endpoints is attained simultaneously by one
actual original-DAG model agreeing on the entire supplied observed law. -/
theorem native_risk_endpoints_attainable (projection : FiniteLatentProjection signature) (graphMatch : HasIVProjection projection)
    (law : FiniteProbRecord signature.Assignment) (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (arms : ArmMarginals law total positive rows columns)
    (controlUpper treatedUpper : Bool) :
    RisksAttainableAt projection law (selectedRisk total positive rows columns controlUpper treatedUpper) := by
  let table := endpointTable total rows columns margins controlUpper treatedUpper
  let responses := endpointResponses total positive rows columns margins table controlUpper treatedUpper
  apply (risksAttainableAt_iff projection graphMatch law _).mpr
  refine ⟨responses, transportationResponses_feasible law total positive rows columns margins arms table
    (endpointFill controlUpper treatedUpper), ?_⟩
  intro action
  exact endpoint_response_risk total positive rows columns margins table controlUpper treatedUpper action
    (endpointTable_attains total rows columns margins controlUpper treatedUpper action)

/-- The application-facing corner theorem computes both margins from the
whole observed law.  Four checked capacity inequalities suffice; neither a
caller-supplied response table nor a preselected native model is required. -/
theorem native_observed_risk_endpoints_attainable (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true)
    (capacities : forall label, observedRows law label + observedColumns law label ≤ observedTotal law)
    (controlUpper treatedUpper : Bool) :
    RisksAttainableAt projection law
      (selectedRisk (observedTotal law) (observedTotal_positive law falsePositive truePositive)
        (observedRows law) (observedColumns law) controlUpper treatedUpper) :=
  native_risk_endpoints_attainable projection graphMatch law (observedTotal law)
    (observedTotal_positive law falsePositive truePositive) (observedRows law) (observedColumns law)
    ⟨observedRows_total law, observedColumns_total law, capacities⟩
    (observedArmMarginals law falsePositive truePositive) controlUpper treatedUpper

end BinaryInstrumental
end Causality
end Thesis
