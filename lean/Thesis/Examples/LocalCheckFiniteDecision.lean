import Thesis.Probability.Core

namespace Thesis.Examples.LocalCheckFiniteDecision

/-!
# A finite kernel-decision resource fixture

Keep the same cached core as the import-only, reflexivity and definition
baselines. This time the new proof asks Lean's kernel to check an exhaustive
four-label decision, like the first case split in transportation. Its domain
is explicitly finite; no general propositional decision principle or native
Boolean proof-reduction axiom is introduced. Failure at a local allocation
cap must not be confused with failure of the theorem in remote verification.
-/

theorem four_labels : ∀ label : Fin 4,
    label.val = 0 ∨ label.val = 1 ∨ label.val = 2 ∨ label.val = 3 := by
  decide +kernel

end Thesis.Examples.LocalCheckFiniteDecision
