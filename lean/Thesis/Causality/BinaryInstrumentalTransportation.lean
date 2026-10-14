import Thesis.Causality.BinaryInstrumentalCoupling
import Thesis.Probability.FourLabelTransportationRecord

namespace Thesis
namespace Causality
namespace BinaryInstrumental

open Probability

/-!
# Relabel actual transportation records to permitted IV couplings

Labels `0,1,2,3` encode `(X,Y)=(false,false),(false,true),(true,false),
and `(true,true)`.  The column outcome is flipped.  Consequently equality
of row and column labels means the original treatment bits agree and their
outcomes differ: precisely the four forbidden IV cells.  Off-diagonal
transportation support is therefore actual response-pair consistency.

The relabelling is explicit and bijective.  Row and column mass formulas
identify the two instrument-arm tables, while every cell's rational weight
is retained.  The subsequent profile lift can fill an unobserved outcome
bit without altering either arm's whole table, using its proved support
condition even when there are zero rows, columns or individual cells.

This module constructs genuine coupling records from supplied natural
tables.  Connecting margins to a fixed observed law, and transporting the
sharp objectives back to native causal queries, remain separate obligations.
-/

def decodeCategory (label : Fin 4) : TreatmentOutcome :=
  if label.val = 0 then (false, false)
  else if label.val = 1 then (false, true)
  else if label.val = 2 then (true, false)
  else (true, true)

def encodeCategory (treatment outcome : Bool) : Fin 4 :=
  if treatment then (if outcome then 3 else 2) else (if outcome then 1 else 0)

theorem decode_encodeCategory (treatment outcome : Bool) : decodeCategory (encodeCategory treatment outcome) = (treatment, outcome) := by
  cases treatment <;> cases outcome <;> rfl

theorem encode_decodeCategory (label : Fin 4) : encodeCategory (decodeCategory label).1 (decodeCategory label).2 = label := by
  rcases FourLabelTransportation.label_cases label with same | same | same | same <;> subst label <;> rfl

def pairOfEdge (edge : Fin 4 × Fin 4) : ResponsePair :=
  (decodeCategory edge.1, ((decodeCategory edge.2).1, !(decodeCategory edge.2).2))

/-- A small closed finite identity checks the actual forbidden-cell map;
it is not an assumed equivalence between causal model families. -/
theorem pairOfEdge_permitted : forall row column : Fin 4,
    permittedPair (pairOfEdge (row, column)) = FourLabelTransportation.offDiagonal (row, column) := by
  decide +kernel

theorem pairOfEdge_cell_false : forall row column : Fin 4, forall treatment outcome : Bool,
    couplingCell false treatment outcome (pairOfEdge (row, column)) = decide (row = encodeCategory treatment outcome) := by
  decide +kernel

theorem pairOfEdge_cell_true : forall row column : Fin 4, forall treatment outcome : Bool,
    couplingCell true treatment outcome (pairOfEdge (row, column)) = decide (column = encodeCategory treatment (!outcome)) := by
  decide +kernel

/-- The genuine table record, pushed through the literal column relabelling.
The original total is kept as its positive rational denominator. -/
def transportationCoupling (total : Nat) (positive : 0 < total)
    (rows columns : FourLabelTransportation.Masses)
    (margins : FourLabelTransportation.Margins total rows columns)
    (table : FourLabelTransportation.Transportation rows columns) : FiniteProbRecord ResponsePair :=
  (FourLabelTransportation.record total positive rows columns margins table).map pairOfEdge

theorem transportationCoupling_permitted (total : Nat) (positive : 0 < total)
    (rows columns : FourLabelTransportation.Masses)
    (margins : FourLabelTransportation.Margins total rows columns)
    (table : FourLabelTransportation.Transportation rows columns) :
    QProb.Equiv ((transportationCoupling total positive rows columns margins table).probVal permittedPair) QProb.one :=
  QProb.equiv_trans ((FourLabelTransportation.record total positive rows columns margins table).map_probVal pairOfEdge permittedPair)
    (QProb.equiv_trans
      ((FourLabelTransportation.record total positive rows columns margins table).probVal_congr _ _
        (fun edge => pairOfEdge_permitted edge.1 edge.2))
      (FourLabelTransportation.record_offDiagonal total positive rows columns margins table))

/-- The first arm uses the unflipped row category. -/
theorem transportationCoupling_cell_false (total : Nat) (positive : 0 < total)
    (rows columns : FourLabelTransportation.Masses)
    (margins : FourLabelTransportation.Margins total rows columns)
    (table : FourLabelTransportation.Transportation rows columns) (treatment outcome : Bool) :
    QProb.Equiv ((transportationCoupling total positive rows columns margins table).probVal (couplingCell false treatment outcome))
      ⟨rows (encodeCategory treatment outcome), total, positive⟩ :=
  QProb.equiv_trans ((FourLabelTransportation.record total positive rows columns margins table).map_probVal pairOfEdge _)
    (QProb.equiv_trans
      ((FourLabelTransportation.record total positive rows columns margins table).probVal_congr _ _
        (fun edge => pairOfEdge_cell_false edge.1 edge.2 treatment outcome))
      (FourLabelTransportation.record_row total positive rows columns margins table _))

/-- The second arm uses the flipped column category.  The explicit flip
prevents accidentally optimizing the wrong risk or signed-effect endpoint. -/
theorem transportationCoupling_cell_true (total : Nat) (positive : 0 < total)
    (rows columns : FourLabelTransportation.Masses)
    (margins : FourLabelTransportation.Margins total rows columns)
    (table : FourLabelTransportation.Transportation rows columns) (treatment outcome : Bool) :
    QProb.Equiv ((transportationCoupling total positive rows columns margins table).probVal (couplingCell true treatment outcome))
      ⟨columns (encodeCategory treatment (!outcome)), total, positive⟩ :=
  QProb.equiv_trans ((FourLabelTransportation.record total positive rows columns margins table).map_probVal pairOfEdge _)
    (QProb.equiv_trans
      ((FourLabelTransportation.record total positive rows columns margins table).probVal_congr _ _
        (fun edge => pairOfEdge_cell_true edge.1 edge.2 treatment outcome))
      (FourLabelTransportation.record_column total positive rows columns margins table _))

end BinaryInstrumental
end Causality
end Thesis
