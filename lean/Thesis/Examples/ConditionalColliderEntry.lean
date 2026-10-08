import Thesis.Examples.ConditionalColliderEntryGraph

namespace Thesis
namespace Causality
namespace Examples
namespace ConditionalColliderEntryRegression

open Probability

/-!
# Actual countermodels with root-specific collider entry kinds

The graph companion proves that the first root permits only observed entry
and the second only shared-latent entry, with both auxiliary sources outside
the queried outcome.  Neither uniform entry family is available.  The general
combined constructor nevertheless selects its actual separated root, finds
that root's entry and directed tail, installs the SCM updates, and returns a
positive countermodel for `P(Y | do(A), R₁,R₂)` on three-valued alphabets.

Only the original hedge and finite eligibility facts are supplied.  The
separated reference, auxiliary source pair, conditional signal gap and all
readout readiness proofs are built internally.  The observational equality
is for the complete law; support is retained at every full-label assignment,
including the third labels checked below.  The semantic statements do not
force the expanded-latent separation computation or claim universal coverage
of arbitrary exhausted IDC paths.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The whole original-query model pair returned by the combined entry
constructor, without choosing which root has the semantic defect. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  witness.positiveConditionalCounterexampleOfRootSpecificColliderEntries rich roots_are_full_condition entries_available

theorem full_observational_equality : ObservationallyEquivalent counterexample.left counterexample.right :=
  counterexample.observationally_equal

theorem original_query_not_identifiable : Not ((GraphModelClass.positive graph).conditionalIdentifiable query) :=
  counterexample.not_identifiable

def thirdReference : signature.Assignment := fun _ => ⟨2, by decide⟩

theorem third_label_cell_positive :
    0 < (counterexample.left.observationalDist.probVal (FiniteProbRecord.singletonEvent thirdReference)).num ∧
    0 < (counterexample.right.observationalDist.probVal (FiniteProbRecord.singletonEvent thirdReference)).num :=
  ⟨counterexample.left_mem.2 thirdReference, counterexample.right_mem.2 thirdReference⟩

end ConditionalColliderEntryRegression
end Examples
end Causality
end Thesis
