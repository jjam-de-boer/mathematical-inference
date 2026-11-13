import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# A concrete label for total finite mechanisms

A normalized finite probability record cannot have an empty atom list.
Reading its first stored label therefore supplies data in the underlying
type, without eliminating a propositional existence proof or invoking choice.
The first atom is deliberately not claimed to have positive weight.

This operation is intended for total structural equations' off-support
fallbacks.  It does not select a probabilistic coupling, certify support,
fill an undefined conditional, or assign a value to division by zero.
Preservation proofs must still show that a fallback cannot change the
required on-support inputs of a constructed model.
-/

/-- Read the first actual stored atom label.  The empty-list case contradicts
positive total mass; no arbitrary inhabitant or positive-atom witness is used. -/
def firstLabel (record : FiniteProbRecord Ω) : Ω := by
  cases atoms : record.atoms with
  | nil =>
      have zero : record.den = 0 := by
        have total := record.total_mass
        rw [atoms] at total
        exact total.symm
      exact False.elim (Nat.ne_of_gt record.den_pos zero)
  | cons head tail => exact head.1

end FiniteProbRecord
end Probability
end Thesis
