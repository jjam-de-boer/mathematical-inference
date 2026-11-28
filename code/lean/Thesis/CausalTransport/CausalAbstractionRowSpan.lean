import Thesis.CausalTransport.CausalAbstractionInverse
import Thesis.Probability.Distros.RationalRowSpan

/-!
# Uniform fine-query identification

An observed singleton after any retained experiment is a linear
functional of the complete fine response law. Include those rows and
normalization. Identification for every pair of rational laws agreeing on
the measurements is exactly one rational row-span test. The values in a
particular dataset are unnecessary for this structural test, and can
force extra equalities on their particular feasible face.
-/

namespace Thesis.Causality.CausalAbstractionInverse.Specification

open Probability Probability.Distros RationalLinear

variable {fine coarse : ObservedSignature.{0}}

/-- Includes every compared coarse singleton and the mass-one row. -/
def measurementRows (spec : Specification fine coarse) :
    List (Fin spec.problem.cells.length → Int) :=
  (fun _ => 1) :: spec.problem.intervals.map (fun row =>
    spec.problem.objectiveCoefficients row.response)

def queryRow (spec : Specification fine coarse) (query : EventQuery fine) :
    Fin spec.problem.cells.length → Int :=
  spec.problem.objectiveCoefficients (eventResponse query.onTable)

/-- Two exact response law vectors can be compared before a dataset is
fixed. The conclusion is stated on the same table order as the solver. -/
theorem uniform_fine_query_iff (spec : Specification fine coarse) (query : EventQuery fine) :
    (∀ left right : Fin spec.problem.cells.length → SignedRatio,
      Simplex left → Simplex right →
      (∀ row ∈ spec.measurementRows, SignedRatio.Equiv
        (dot _ row left) (dot _ row right)) →
      SignedRatio.Equiv (dot _ (spec.queryRow query) left) (dot _ (spec.queryRow query) right)) ↔
    RationalSpan spec.measurementRows (spec.queryRow query) :=
  uniform_simplex_iff_rationalSpan _ _ (List.mem_cons_self ..)

end Thesis.Causality.CausalAbstractionInverse.Specification
