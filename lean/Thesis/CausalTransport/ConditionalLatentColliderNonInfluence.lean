import Thesis.CausalTransport.ConditionalLatentCollider
import Thesis.Causality.PrivateNoiseNonInfluence

namespace Thesis
namespace Causality

open Probability

/-!
# Readout readiness of the actual shared-latent collider

The shared mask is an incident latent input, not an observed parent read.
Its first update therefore preserves every initially ignored observed
coordinate.  The child's later private replacement reads that same latent
mask and its old full output, retaining all background labels.  Agreement
away from an ignored observed coordinate preserves the old output while
the latent mask and private noise remain fixed.

This mechanism-level argument needs no ambient ordering between the
collider and a future route destination.  Unlike the observed-parent
collider, it does not introduce a new observed dependence on the displayed
parent, so that parent is not an exception to the preserved invariant.
Neither compatibility nor positivity is inferred here: those remain the
separate proved properties of the actual collider construction.
-/

variable {S : ObservedSignature.{0}}

namespace ConditionalLatentCollider

/-- The complete shared-mask/private-noise update preserves every initially
ignored observed coordinate.  The new shared bit is held fixed as a latent
input, and the base invariant controls the retained full-value background. -/
theorem model_otherMechanismsIgnore (base : ExactModel S)
    (rich : ObservedSignature.ValueRich S) (parent child : Fin S.count)
    (noise : FiniteProbRecord Bool) (node : Fin S.count)
    (ignored : base.OtherMechanismsIgnore node) :
    (model base rich parent child noise).OtherMechanismsIgnore node := by
  have masked := base.withSharedReadout_otherMechanismsIgnore parent child node
    ColliderChannel.fairMask (maskReadout rich parent) ignored
  apply (maskModel base rich parent child).withPrivateBooleanNoise_otherMechanismsIgnore_of_replacement
    child node noise (replacement base rich parent child) masked
  intro different first second inputs bit agree
  have old : (maskModel base rich parent child).mechanism child first inputs =
      (maskModel base rich parent child).mechanism child second inputs :=
    masked child different first second inputs agree
  simp only [replacement, old]

end ConditionalLatentCollider
end Causality
end Thesis
