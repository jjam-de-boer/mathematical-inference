import Thesis.Causality.Structural.Core
import Thesis.Causality.Structural.Atomic

namespace Thesis
namespace Causality

open Probability

/-! Compact structural surgery and its equivalence with atomic execution. -/

namespace AtomicIntervention

/--
The direct surgical constructor is a convenience/reference presentation of the
same unit-level operation computed by the dependent-signature atomic edit path.
-/
theorem compile_semanticallyEquivalent_surgery (mode : CausalMode S)
    (action : Action S) (assignment : mode.record.model.latent.Assignment) :
    Exists fun targetAssignment :
        (compile mode action).target.record.model.latent.Assignment =>
      (compile mode action).target.record.model.eval targetAssignment =
        (compile mode action).transportedObserved
          ((SurgicalIntervention.model mode.record.model action).eval assignment) := by
  rcases (compileRealizes mode action).evaluate assignment with
    ⟨targetAssignment, evaluated⟩
  refine ⟨targetAssignment, ?_⟩
  rw [SurgicalIntervention.eval_eq_evalUnder]
  exact evaluated

end AtomicIntervention

end Causality
end Thesis
