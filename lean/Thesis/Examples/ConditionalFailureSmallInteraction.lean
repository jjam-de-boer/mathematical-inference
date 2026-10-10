import Thesis.Examples.ConditionalFailureSmallInteractionGraph

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureSmallInteraction

open Probability PathSpecification FiniteBooleanInteraction HedgeChannelEnvironmentInstallation
open CurrentConditionalFailureActivationSelection

/-!
# A complete original conditional countermodel from the actual normal form

The graph companion proves all-Small coverage of the actual opaque normalized
path/activation construction, completed with the original conditioners.
Here that construction supplies the legal signal, supported direction, actual
outcome character, even outside-Small rows and complete cylinder conservation.
The parity adapter derives oddness of the *whole* original Small forest.

The covariance theorem then constructs a fully positive observationally
equivalent pair on all original three-valued alphabets, with a gap for the
unchanged query `P(Y | do(X),P,Z)`.  Both evidence masses are retained.
Unlike the earlier explicit-mask fixture, no hand-written alternative signal,
literal direction or finite conservation/parity certificate is supplied.

This closes a genuine normalized-interaction instance and its complete Small
phase.  It does not establish universal graph coverage: other terminals may
have unconditioned missing Small rows or a latest pivot outside Small.
-/

/-- The actual fused signal, including its original reserved inputs. -/
def installed : LinearSignal graph := normal.activationInteractionSignal pivot.toRetained forest.toCutForest

/-- All actual graph membership/coverage certificates are supplied by
the companion.  Every parity and matching field is a constructed theorem. -/
def parityWitness : ConditionalParityWitness witness installed installed :=
  .ofNormalizedActivation witness pivot.toRetained normal forest.toCutForest pivot_in_small actual_small_coverage

/-- This is oddness of every mandatory Small row's installed phase, not
just of the path-head union or its pivot.  It is derived by conservation. -/
theorem complete_small_phase_odd : (installed.forestPhase witness.small).value normal.pathDirection = true :=
  parityWitness.small_odd

/-- The exact outside-Small background retains the completed interaction's
remaining rows once.  No Small/activation disjointness is imposed. -/
theorem actual_selected_background : parityWitness.selected =
    NodeSet.diff (normal.smallInteractionRows pivot.toRetained forest.toCutForest) witness.small := rfl

/-- The actual covariance identity holds throughout the original evidence
cylinder, including every free original reserved coordinate and outcome. -/
theorem full_original_cylinder_matching (point : Cube graph)
    (listed : point ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition))) :
    ((installed.forestPhase witness.small).xor (maskPhase _ parityWitness.outcomeMask)).value point =
      (selectedPhase _ signature.count parityWitness.selected installed.rowPhase).value point :=
  parityWitness.matching point listed

/-- Positive original-alphabet models with complete observational equality
and a strict gap for the unchanged conditional query follow from the actual
normalized construction.  No finite probability-table enumeration is used. -/
noncomputable def counterexample : ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  conditionalCounterexampleOfNormalizedActivation witness rich pivot.toRetained normal forest.toCutForest pivot_in_small actual_small_coverage

/-- The constructed pair refutes identifiability of the unchanged query
in the fully positive class, not just identifiability of its numerator. -/
theorem query_not_identifiable : ¬ (GraphModelClass.positive graph).conditionalIdentifiable query :=
  counterexample.not_identifiable

end CurrentConditionalFailureSmallInteraction
end Examples
end Causality
end Thesis
