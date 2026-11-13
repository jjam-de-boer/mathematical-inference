import Thesis.Probability.Core

namespace Thesis.Examples.LocalCheckDefinition

/-!
# A small definition after the probability-core import

The import is identical to the other core-based resource fixtures. The new
definition uses only natural-number recursion, with no search, normalization
proof, finite product or causal construction. A cap failure here would locate
a boundary earlier than the large soundness/completeness proof infrastructure.
The definition is checked normally by remote CI and the transitive axiom gate;
its role in this file is diagnostic, not a new probability theorem.
-/

/-- A deliberately elementary recursive term for the kernel-checking pilot. -/
def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

end Thesis.Examples.LocalCheckDefinition
