import Thesis.CausalTransport.BinaryInstrumentalObservedMargins
import Thesis.Causality.BinaryInstrumentalRiskEvents

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability
open FourLabelTransportation

/-!
# Every native IV model supplies the scaled transportation table

Extract the actual response record of the original native model, relabel its
coupling, and aggregate its real singleton masses.  Its denominator is kept
independent of the common observed-arm total.  Positivity of both observed
instrument masses permits cancellation of their coefficients in the joint
cell equations; no treatment/outcome cell is required to be positive.

Multiplying the actual table's weights by the observed total gives margins
equal to the observed margins times the unknown response denominator.  The
universal scaled-capacity theorem therefore applies to *every* native model
with the fixed whole law, not only the integer-grid endpoint construction.

This also proves necessity of the four computed instrument inequalities.
The reverse direction constructs an actual model from the transportation
algorithm, yielding exact compatibility when both instrument values occur.
The null-instrument branch and the final risk/effect objectives are separate
obligations and are not hidden behind a positivity assumption here.
-/

variable {P : FiniteLatentProjection signature}

private theorem positive_mul_cancel (factor left right : QProb) (positive : 0 < factor.num)
    (same : QProb.Equiv (QProb.mul factor left) (QProb.mul factor right)) : QProb.Equiv left right := by
  have cleared : (factor.num * factor.den) * (left.num * right.den) =
      (factor.num * factor.den) * (right.num * left.den) := by
    calc
      _ = (factor.num * left.num) * (factor.den * right.den) := by ac_rfl
      _ = (factor.num * right.num) * (factor.den * left.den) := same
      _ = _ := by ac_rfl
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos positive factor.den_pos) cleared

def nativeEdgeRecord (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P) :
    FiniteProbRecord (Fin 4 × Fin 4) :=
  (responseCoupling (responseRepresentation native graphMatch).responses).map edgeOfPair

theorem nativeEdgeRecord_offDiagonal (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P) :
    QProb.Equiv ((nativeEdgeRecord native graphMatch).probVal offDiagonal) QProb.one :=
  edge_relabel_offDiagonal _ (responseCoupling_permitted (responseRepresentation native graphMatch).responses)

theorem nativeEdgeRecord_row (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P) (row : Fin 4) :
    QProb.Equiv ((nativeEdgeRecord native graphMatch).probVal (rowEvent row))
      ((responseRepresentation native graphMatch).responses.probVal
        (responseCell false (decodeCategory row).1 (decodeCategory row).2)) :=
  QProb.equiv_trans ((responseCoupling (responseRepresentation native graphMatch).responses).map_probVal edgeOfPair (rowEvent row))
    (QProb.equiv_trans
      ((responseCoupling (responseRepresentation native graphMatch).responses).probVal_congr _ _
        (fun pair => edgeOfPair_row_match pair row))
      (responseCoupling_cell _ false (decodeCategory row).1 (decodeCategory row).2))

theorem nativeEdgeRecord_column (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P) (column : Fin 4) :
    QProb.Equiv ((nativeEdgeRecord native graphMatch).probVal (columnEvent column))
      ((responseRepresentation native graphMatch).responses.probVal
        (responseCell true (decodeCategory column).1 (!(decodeCategory column).2))) :=
  QProb.equiv_trans ((responseCoupling (responseRepresentation native graphMatch).responses).map_probVal edgeOfPair (columnEvent column))
    (QProb.equiv_trans
      ((responseCoupling (responseRepresentation native graphMatch).responses).probVal_congr _ _
        (fun pair => edgeOfPair_column_match pair column))
      (responseCoupling_cell _ true (decodeCategory column).1 (!(decodeCategory column).2)))

/-- The actual row weights match the fixed observed margins only after
cross multiplication by both genuine denominators. -/
theorem native_row_relation (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (arms : ArmMarginals law total positive rows columns) (falsePositive : 0 < instrumentMass law false) (row : Fin 4) :
    aggregateRows (nativeEdgeRecord native graphMatch) row * total = rows row * (nativeEdgeRecord native graphMatch).den := by
  have actual := native_responses_feasible native graphMatch law observed false (decodeCategory row).1 (decodeCategory row).2
  have fixed := arms.false_cells (decodeCategory row).1 (decodeCategory row).2
  simp only [encode_decodeCategory] at fixed
  have actualEdge := QProb.equiv_trans actual
    (QProb.mul_congr (QProb.equiv_refl _) (QProb.equiv_symm (nativeEdgeRecord_row native graphMatch row)))
  have multiplierPositive := (QProb.equiv_num_pos_iff (instrumentMarginal_probVal law false)).mpr falsePositive
  exact positive_mul_cancel ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent false))
    ((nativeEdgeRecord native graphMatch).probVal (rowEvent row)) ⟨rows row, total, positive⟩
    multiplierPositive (QProb.equiv_trans (QProb.equiv_symm actualEdge) fixed)

theorem native_column_relation (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (arms : ArmMarginals law total positive rows columns) (truePositive : 0 < instrumentMass law true) (column : Fin 4) :
    aggregateColumns (nativeEdgeRecord native graphMatch) column * total = columns column * (nativeEdgeRecord native graphMatch).den := by
  have actual := native_responses_feasible native graphMatch law observed true (decodeCategory column).1 (!(decodeCategory column).2)
  have fixed := arms.true_cells (decodeCategory column).1 (!(decodeCategory column).2)
  simp only [Bool.not_not, encode_decodeCategory] at fixed
  have actualEdge := QProb.equiv_trans actual
    (QProb.mul_congr (QProb.equiv_refl _) (QProb.equiv_symm (nativeEdgeRecord_column native graphMatch column)))
  have multiplierPositive := (QProb.equiv_num_pos_iff (instrumentMarginal_probVal law true)).mpr truePositive
  exact positive_mul_cancel ((instrumentMarginal law).probVal (FiniteProbRecord.singletonEvent true))
    ((nativeEdgeRecord native graphMatch).probVal (columnEvent column)) ⟨columns column, total, positive⟩
    multiplierPositive (QProb.equiv_trans (QProb.equiv_symm actualEdge) fixed)

/-- The weights come from the arbitrary original model, not from the
observed-denominator grid.  Only their margins are proved to agree after
scaling; the actual singleton weights need not be multiples of that grid. -/
def nativeScaledTable (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (arms : ArmMarginals law total positive rows columns)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) :
    Transportation (fun label => rows label * (nativeEdgeRecord native graphMatch).den)
      (fun label => columns label * (nativeEdgeRecord native graphMatch).den) where
  cells := fun row column => aggregateCells (nativeEdgeRecord native graphMatch) row column * total
  row_sum := fun row => (sum4_scale (aggregateCells (nativeEdgeRecord native graphMatch) row) total).trans
    ((congrArg (fun mass => mass * total) (aggregate_row_sum (nativeEdgeRecord native graphMatch) row)).trans
      (native_row_relation native graphMatch law observed total positive rows columns arms falsePositive row))
  column_sum := fun column => (sum4_scale (fun row => aggregateCells (nativeEdgeRecord native graphMatch) row column) total).trans
    ((congrArg (fun mass => mass * total) (aggregate_column_sum (nativeEdgeRecord native graphMatch) column)).trans
      (native_column_relation native graphMatch law observed total positive rows columns arms truePositive column))
  diagonal_zero := fun label => by
    rw [aggregate_diagonal_zero _ (nativeEdgeRecord_offDiagonal native graphMatch) label, Nat.zero_mul]

/-- Universal rational cell bound for every compatible original-DAG model.
This is a semantic all-model theorem, not only a bound on integer candidates. -/
theorem native_cell_bound (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (total : Nat) (positive : 0 < total) (rows columns : Masses)
    (margins : Margins total rows columns) (arms : ArmMarginals law total positive rows columns)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true)
    (edge : Fin 4 × Fin 4) (different : edge.1 ≠ edge.2) :
    QProb.LE ((nativeEdgeRecord native graphMatch).probVal (FiniteProbRecord.singletonEvent edge))
      ⟨edgeCapacity total rows columns edge, total, positive⟩ :=
  scaled_cell_bound total rows columns margins (nativeEdgeRecord native graphMatch).den edge different
    (nativeScaledTable native graphMatch law observed total positive rows columns arms falsePositive truePositive)

/-- A native model's existence forces the computed instrument inequalities.
Cancellation uses its actual positive response denominator, not the positivity
of any individual cell in the observed or intervened distributions. -/
theorem native_observed_capacities (native : FiniteHiddenDAGSCM signature P) (graphMatch : HasIVProjection P)
    (law : FiniteProbRecord signature.Assignment) (observed : HasObservedLaw native law)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) :
    forall label, observedRows law label + observedColumns law label ≤ observedTotal law := by
  let source := nativeEdgeRecord native graphMatch
  let table := nativeScaledTable native graphMatch law observed (observedTotal law)
    (observedTotal_positive law falsePositive truePositive) (observedRows law) (observedColumns law)
    (observedArmMarginals law falsePositive truePositive) falsePositive truePositive
  have rowsTotal := (sum4_scale (observedRows law) source.den).trans
    (congrArg (fun mass => mass * source.den) (observedRows_total law))
  have capacity := transportation_capacity (observedTotal law * source.den) _ _ rowsTotal table
  intro label
  have bounded := capacity label
  rw [← Nat.add_mul] at bounded
  exact (Nat.mul_le_mul_right_iff source.den_pos).mp bounded

/-- Exact compatibility of a supplied whole law with the original IV DAG
in the both-nonnull-instrument branch.  All other observed zeros are allowed. -/
theorem nativeModelExists_iff_observed_capacities (projection : FiniteLatentProjection signature)
    (graphMatch : HasIVProjection projection) (law : FiniteProbRecord signature.Assignment)
    (falsePositive : 0 < instrumentMass law false) (truePositive : 0 < instrumentMass law true) :
    (∃ native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native law) ↔
      forall label, observedRows law label + observedColumns law label ≤ observedTotal law := by
  constructor
  · rintro ⟨native, observed⟩
    exact native_observed_capacities native graphMatch law observed falsePositive truePositive
  · intro capacity
    let margins : Margins (observedTotal law) (observedRows law) (observedColumns law) :=
      ⟨observedRows_total law, observedColumns_total law, capacity⟩
    let table := transport (observedTotal law) (observedRows law) (observedColumns law) margins
    exact ⟨transportationNativeModel projection graphMatch law (observedTotal law)
        (observedTotal_positive law falsePositive truePositive) (observedRows law) (observedColumns law) margins table (fun _ => false),
      transportationNativeModel_hasObservedLaw projection graphMatch law (observedTotal law)
        (observedTotal_positive law falsePositive truePositive) (observedRows law) (observedColumns law) margins
        (observedArmMarginals law falsePositive truePositive) table (fun _ => false)⟩

end BinaryInstrumental
end Causality
end Thesis
