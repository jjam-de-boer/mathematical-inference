import Thesis.Examples.ConditionalReadoutGraph

namespace Thesis
namespace Causality
namespace Examples
namespace ConditionalReadoutRegression

open Probability

/-!
# A genuine conditional failure carried through two observed readout arrows

`ConditionalReadoutGraph` contains the graph and finite availability proofs.
This module checks the actual SCM pair in a separate compiler process.

The topological order is `U,A,R,M,Y,E`.  The edges are `U -> R <- A`,
`A <-> R`, and the route `U -> M -> Y`; `E` is isolated.  All observed
alphabets have three labels.  The actual target is
`P(Y,E | do(A), R)`, and neither `U` nor `M` belongs to its queried outcome.

The hedge belongs to the original target's numerator.  The general constructor
selects its separated root, finds the auxiliary parent and both readout arrows,
constructs the auxiliary collider countermodel and proves route readiness.
The seed pair, source reference, numerical gap and intermediate SCM invariants
are not supplied by the fixture.  Every step retains the whole original action
and conditioner; the final extra outcome is restored by marginalization.

`ConditionalReadoutFailure` derives actual IDC failure from this independently
constructed countermodel, success soundness and termination.  The semantic
regression here does not reevaluate the expanded-latent separation matrix in
the kernel.  `ConditionalReadoutPaths` retains the separate exact fail-record and
searched back-door path checks, and compares the generated route's endpoints
and destinations numerically.  Those forced-data computations are not needed
to check the semantic constructor here.  General mixed active paths and
collider activation remain open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem readouts_not_queried : target.outcome parent = false ∧ target.outcome middle = false ∧
    target.outcome outcome = true ∧ target.outcome extraOutcome = true := by decide +kernel

/-! ## Whole-query positive countermodels -/

/-- Actual positive models for the whole original query.  The general
constructor selects both the separated source cell and graph route internally;
the fixture supplies only the original hedge and checked graph availability. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) target :=
  witness.positiveConditionalCounterexampleOfRootSpecificColliderRoutes rich roots_are_root routes_available

theorem full_observational_equality : ObservationallyEquivalent counterexample.left counterexample.right :=
  counterexample.observationally_equal

theorem original_query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable target) :=
  counterexample.not_identifiable

def thirdReference : signature.Assignment := fun _ => ⟨2, by decide⟩

theorem third_label_cell_positive :
    0 < (counterexample.left.observationalDist.probVal (FiniteProbRecord.singletonEvent thirdReference)).num ∧
    0 < (counterexample.right.observationalDist.probVal (FiniteProbRecord.singletonEvent thirdReference)).num :=
  ⟨counterexample.left_mem.2 thirdReference, counterexample.right_mem.2 thirdReference⟩

end ConditionalReadoutRegression
end Examples
end Causality
end Thesis
