import Thesis.CausalTransport.BinaryInstrumental.NativeTransportation
import Thesis.Examples.BinaryInstrumental.Transportation

namespace Thesis
namespace Causality
namespace Examples
namespace BinaryInstrumentalCompatibility

open Probability BinaryInstrumental FourLabelTransportation

/-!
# Computed IV compatibility and universal native-cell regressions

Uniform observed data have computed common total sixteen and four units
in each normalized row and column.  The numeric capacity check constructs
an actual model on the original hidden DAG.  The rational cell upper bound
is also applied to an arbitrary native model with this whole law, keeping
its hidden alphabets and response denominator unrestricted.

The second law has a fair instrument, constant treatment, and outcome equal
to the instrument.  It violates exclusion: in row/column label zero the two
computed masses sum to two while the total is one.  The all-model necessity
theorem therefore excludes *every* native IV model with that law.  It does
not mistake incompatible observations for a vacuous sharply identified value.
Both laws allow observed zeros; only instrument masses are positive here.
-/

abbrev projection := BinaryInstrumentalRepresentation.projection
theorem projected_iv_graph : HasIVProjection projection := BinaryInstrumentalRepresentation.projected_iv_graph
abbrev uniformLaw := BinaryInstrumentalTransportation.uniformLaw

theorem uniform_false_positive : 0 < instrumentMass uniformLaw false := by decide +kernel
theorem uniform_true_positive : 0 < instrumentMass uniformLaw true := by decide +kernel

theorem uniform_capacities : forall label,
    observedRows uniformLaw label + observedColumns uniformLaw label ≤ observedTotal uniformLaw := by decide +kernel

theorem uniform_native_exists : ∃ native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native uniformLaw :=
  (nativeModelExists_iff_observed_capacities projection projected_iv_graph uniformLaw
    uniform_false_positive uniform_true_positive).mpr uniform_capacities

def uniformMargins : Margins (observedTotal uniformLaw) (observedRows uniformLaw) (observedColumns uniformLaw) :=
  ⟨observedRows_total uniformLaw, observedColumns_total uniformLaw, uniform_capacities⟩

/-- No response-denominator or native-cardinality restriction is assumed
about this arbitrary model.  The quarter bound comes from computed data. -/
theorem uniform_native_cell_bound (native : FiniteHiddenDAGSCM signature projection)
    (observed : HasObservedLaw native uniformLaw) :
    QProb.LE ((nativeEdgeRecord native projected_iv_graph).probVal (FiniteProbRecord.singletonEvent (0, 1)))
      BinaryInstrumentalTransportation.quarter := by
  have bounded := native_cell_bound native projected_iv_graph uniformLaw observed (observedTotal uniformLaw)
    (observedTotal_positive uniformLaw uniform_false_positive uniform_true_positive)
    (observedRows uniformLaw) (observedColumns uniformLaw) uniformMargins
    (observedArmMarginals uniformLaw uniform_false_positive uniform_true_positive)
    uniform_false_positive uniform_true_positive (0, 1) (by decide)
  have endpoint : QProb.Equiv
      (⟨edgeCapacity (observedTotal uniformLaw) (observedRows uniformLaw) (observedColumns uniformLaw) (0, 1),
        observedTotal uniformLaw, observedTotal_positive uniformLaw uniform_false_positive uniform_true_positive⟩ : QProb)
      BinaryInstrumentalTransportation.quarter := by decide +kernel
  exact QProb.le_congr (QProb.equiv_refl _) endpoint bounded

def assignment (instrument treatment outcome : Bool) : signature.Assignment :=
  fun node => if node.val = 0 then instrument else if node.val = 1 then treatment else outcome

def excludedLaw : FiniteProbRecord signature.Assignment :=
  ⟨[(assignment false false false, 1), (assignment true false true, 1)], 2, by decide, rfl⟩

theorem excluded_false_positive : 0 < instrumentMass excludedLaw false := by decide +kernel
theorem excluded_true_positive : 0 < instrumentMass excludedLaw true := by decide +kernel

theorem excluded_native_impossible : ¬ ∃ native : FiniteHiddenDAGSCM signature projection, HasObservedLaw native excludedLaw := by
  intro purported
  have capacities := (nativeModelExists_iff_observed_capacities projection projected_iv_graph excludedLaw
    excluded_false_positive excluded_true_positive).mp purported
  have violation : ¬ (observedRows excludedLaw 0 + observedColumns excludedLaw 0 ≤ observedTotal excludedLaw) := by decide +kernel
  exact violation (capacities 0)

end BinaryInstrumentalCompatibility
end Examples
end Causality
end Thesis
