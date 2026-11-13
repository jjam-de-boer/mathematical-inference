import Thesis.Probability.FourLabelTransportationAggregation

namespace Thesis
namespace Probability
namespace Examples
namespace FourLabelTransportationAggregation

open Thesis.Probability.FourLabelTransportation

/-!
# Aggregation retains repeated labels and zero-weight forbidden cells

The first off-diagonal pair occurs twice, with weights one and two.  A
forbidden diagonal pair is also listed, but its weight is zero.  Aggregation
must collect the former into mass three without demanding literal support
membership from the latter.  The original denominator four is retained.

The universal theorem proves agreement on every event of these records;
the small numerical decisions below check only the displayed source data.
-/

def repeated : FiniteProbRecord (Fin 4 × Fin 4) :=
  ⟨[((0, 1), 1), ((0, 1), 2), ((1, 0), 1), ((0, 0), 0)], 4, by decide, rfl⟩

theorem repeated_permitted : QProb.Equiv (repeated.probVal offDiagonal) QProb.one := by decide +kernel

def table : Transportation (aggregateRows repeated) (aggregateColumns repeated) := aggregateTable repeated repeated_permitted

theorem repeated_mass : table.cells 0 1 = 3 := by decide +kernel
theorem listed_diagonal_zero : table.cells 0 0 = 0 := table.diagonal_zero 0

theorem whole_law_preserved (event : Event (Fin 4 × Fin 4)) :
    QProb.Equiv
      ((record repeated.den repeated.den_pos (aggregateRows repeated) (aggregateColumns repeated)
        (aggregateMargins repeated repeated_permitted) table).probVal event)
      (repeated.probVal event) := aggregated_record_preserves repeated repeated_permitted event

end FourLabelTransportationAggregation
end Examples
end Probability
end Thesis
