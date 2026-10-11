import Thesis.Causality.SupportAwareTerms

namespace Thesis
namespace Causality

open Probability

/-!
# Kernel chains across zero conditioning cells

This is the first kernel-level use of the guarded expression constructor.
The whole chain is an identity in one finite SCM, with its original action
and base conditioner retained.  It is not an identification theorem and does
not replace a graph-dependent do-rule.  No global positivity, compatibility,
or externally assumed probability identity is used.

All three kernels share the same intervened distribution.  Their numerators
and conditioners are then aligned with three actual cylinder events.  Event
containment discharges the zero-middle premise of `weightedDivide_chain`.
Thus a zero middle cylinder under a supported base contributes zero, while
a zero base leaves both complete kernels undefined.  The intervened
distribution may contain arbitrary zeros.
-/

namespace ProbabilityTerm

/-! `ProbabilityTerm.weightedChain_soundAt` now lives beside the intrinsic
term semantics, so ordinary derivations and finite source transport use the
same proved probability identity.  This module remains the stable transport
import boundary; it does not introduce another copy or assumed law. -/

end ProbabilityTerm
end Causality
end Thesis
