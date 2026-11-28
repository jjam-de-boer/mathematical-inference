import Thesis.CausalTransport.CausalAbstractionInverseConditional
import Thesis.CausalTransport.ResponseOrbitReduction

/-!
# Orbit-reduced fine-query solving

The solver takes a group action on fine response tables. It computes the
subgroup fixing the retained measurement rows and requested events. A
moved query therefore restricts its own stabilizer even when the data are
symmetric. Reduced results have the original specification's type and
refer to actual fine models and its original support conditions.
-/

namespace Thesis.Causality.CausalAbstractionInverse.Specification

open Probability Probability.Distros FiniteSymmetry ResponseOrbitReduction

variable {fine coarse : ObservedSignature.{0}} {G : Group}

def orbitReduction (spec : Specification fine coarse) (action : Action G (SharedResponse.Table fine))
    (events : List (Event (SharedResponse.Table fine))) : Reduction G spec.problem :=
  ⟨action, SharedResponse.enumeration_complete fine, events⟩

private theorem orbitInfeasible (spec : Specification fine coarse) (reduction : Reduction G spec.problem)
    (certificate : RationalLinear.Infeasibility reduction.problem.cells.length reduction.problem.rows) :
    ¬ ∃ model : ExactModel fine, spec.Fits model := by
  rintro ⟨model, fits⟩
  let law : Distro (SharedResponse.Table fine) := ⟨SharedResponse.lawOf fine model⟩
  exact reduction.infeasible_not_compatible certificate
    ⟨law, (spec.moments_iff_responseFits law).mpr (spec.responseFits_of_fits model fits)⟩

/-- The bound is computed on one mass per orbit, then certified for every
compatible fine model. Each endpoint includes a fine witness. -/
def solveQueryWithOrbits (spec : Specification fine coarse) (action : Action G (SharedResponse.Table fine))
    (query : EventQuery fine) : spec.QueryResult query :=
  if valid : spec.Valid then
    let reduction := spec.orbitReduction action [query.onTable]
    match reduction.problem.solveEventBounds query.onTable with
    | .infeasible certificate => .incompatible valid (spec.orbitInfeasible reduction certificate)
    | .bounded bounds =>
      let sharp := spec.queryBoundsOfMoment query
        (reduction.restoreBounds query.onTable (List.mem_singleton_self _) bounds)
      if same : SignedRatio.Equiv sharp.lower sharp.upper then .point valid sharp same
      else .interval valid sharp same
  else .invalid valid

/-- Register the conditioner and the joint numerator event. Marginal
evidence bounds retain zero and positive support, and conditional range
optimization retains the correct joint numerator. -/
def solveConditionalWithOrbits (spec : Specification fine coarse)
    (action : Action G (SharedResponse.Table fine)) (evidence query : EventQuery fine) :
    spec.ConditionalResult evidence query :=
  if valid : spec.Valid then
    let numerator := fun table => evidence.onTable table && query.onTable table
    let reduction := spec.orbitReduction action [evidence.onTable, numerator]
    match reduction.problem.solveEventBounds evidence.onTable with
    | .infeasible certificate => .incompatible valid (spec.orbitInfeasible reduction certificate)
    | .bounded bounds =>
      let evidenceListed : evidence.onTable ∈ reduction.events := List.mem_cons_self ..
      let numeratorListed : numerator ∈ reduction.events := List.mem_cons_of_mem _ (List.mem_singleton_self _)
      spec.conditionalResultOfBounds valid evidence query
        (reduction.restoreBounds evidence.onTable evidenceListed bounds) (fun reference =>
          reduction.restoreConditionalRange evidence.onTable query.onTable evidenceListed numeratorListed
            (reduction.problem.conditionalRange evidence.onTable query.onTable
              (reduction.compressConditional evidence.onTable evidenceListed reference)))
  else .invalid valid

end Thesis.Causality.CausalAbstractionInverse.Specification
