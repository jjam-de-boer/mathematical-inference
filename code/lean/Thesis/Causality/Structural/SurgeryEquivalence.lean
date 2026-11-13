import Thesis.Causality.Structural.Core
import Thesis.Causality.Structural.AtomicExecution

namespace Thesis
namespace Causality

open Probability

/-!
Semantic agreement between the compact surgical reference construction and the
expanded atomic edit program.

This small module is separated from `SurgeryCore`: the latter defines compact
surgery itself, while this module depends on `Atomic` to prove that its longer
proof-carrying compilation has the same unit-level effect.
-/

namespace AtomicIntervention

/--
The canonical endpoint assignment retained by atomic compilation evaluates to
the compact surgical model's value for the same source latent unit.
-/
theorem compileDeterministicRealizes_evaluate_surgery
    (mode : CausalMode S) (action : Action S)
    (assignment : mode.record.model.latent.Assignment) :
    (compile mode action).target.record.model.eval
        ((compileDeterministicRealizes mode action).assignment assignment) =
      (compile mode action).transportedObserved
        ((SurgicalIntervention.model mode.record.model action).eval
          assignment) := by
  rw [SurgicalIntervention.eval_eq_evalUnder]
  exact (compileDeterministicRealizes mode action).evaluate assignment

/--
The direct surgical constructor is a convenience/reference presentation of the
same unit-level operation computed by the dependent-signature atomic edit path.
The existential statement packages the canonical assignment from
`compileDeterministicRealizes`.
-/
theorem compile_semanticallyEquivalent_surgery (mode : CausalMode S)
    (action : Action S) (assignment : mode.record.model.latent.Assignment) :
    Exists fun targetAssignment :
        (compile mode action).target.record.model.latent.Assignment =>
      (compile mode action).target.record.model.eval targetAssignment =
        (compile mode action).transportedObserved
          ((SurgicalIntervention.model mode.record.model action).eval assignment) := by
  exact ⟨(compileDeterministicRealizes mode action).assignment assignment,
    compileDeterministicRealizes_evaluate_surgery mode action assignment⟩

end AtomicIntervention

end Causality
end Thesis
