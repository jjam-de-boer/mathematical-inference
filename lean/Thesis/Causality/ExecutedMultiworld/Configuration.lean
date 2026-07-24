import Thesis.Causality.Multiworld
import Thesis.Causality.Structural.Atomic

namespace Thesis
namespace Causality

open Probability

/-!
Route-independent interface for a configured occurrence multiworld.

The from-factual and from-empty programs have different creation paths and
therefore different dependent endpoint signatures.  Once a route has installed
its copied equations, however, both expose the same information: a coordinate
transport, a source-root assignment transport, a simultaneous action, and a
unit-level comparison with the reference occurrence evaluator.
-/

structure MultiworldConfiguration (M : ExactModel S)
    (event : CounterfactualEvent S) where
  signature : ObservedSignature
  record : CausalEpistemicRecord signature
  coordinates : AtomicIntervention.SameCoordinates
    (OccurrenceMultiworld.Encoding.signature (M.occurrenceMultiworld event))
    signature
  rootAssignment : M.latent.Assignment -> record.model.latent.Assignment
  action : AtomicIntervention.Action signature
  evaluatesAsReference : forall assignment,
    record.model.evalUnder action (rootAssignment assignment) =
      coordinates.transportObserved
        (OccurrenceMultiworld.Encoding.encodeAssignment
          (M.occurrenceMultiworld event)
          ((M.occurrenceMultiworld event).eval assignment))

end Causality
end Thesis
