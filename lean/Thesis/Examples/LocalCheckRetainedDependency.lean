import Thesis.Examples.LocalCheckDefinition

namespace Thesis.Examples.LocalCheckRetainedDependency

/-!
# A new proof importing an independently retained local definition

The capped local-check helper can compile `LocalCheckDefinition`, retain its
actual `.olean`, then import it here without rebuilding it or fabricating a
Lake trace. This deliberately small client distinguishes a usable dependency
cache from merely remembering that some earlier command returned success.
Both files still belong to the complete remote build and transitive axiom
audit. Local reuse does not replace either gate.
-/

/-- A genuinely new kernel-checked proof over the retained recursive term. -/
theorem triangle_three : LocalCheckDefinition.triangle 3 = 6 := rfl

/-- Adding this second proof exercises source-key invalidation: the earlier
retained client cannot stand in for checking a newly edited source file. -/
theorem triangle_four : LocalCheckDefinition.triangle 4 = 10 := rfl

end Thesis.Examples.LocalCheckRetainedDependency
