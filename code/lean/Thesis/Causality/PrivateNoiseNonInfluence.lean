import Thesis.Causality.PrivateNoise

namespace Thesis
namespace Causality

open Probability

/-!
# Non-influence under a parent-respecting private replacement

An earlier replacement cannot acquire a later observed parent.  That existing
topological argument is sufficient for an increasing readout plan, but is too
coarse for a collider followed by a route: a route destination can occur before
the conditioned collider in the ambient order.  The ambient signature may even
allow an arrow from that destination into the collider which its actual
replacement does not read.

The semantic criterion here inspects the replacement itself.  If agreement of
declared parent inputs away from an ignored coordinate gives the same new
output, then the update preserves non-influence of that coordinate.  Both old
latent inputs and the new private bit are held fixed.  No new independence
assumption about the augmented prior, or absence of an allowed edge, is used.

The condition is needed only when the updated and ignored vertices differ.
Updating the ignored vertex itself leaves all the other mechanisms unchanged,
so its replacement needs no additional condition in that branch.
-/

variable {S : ObservedSignature.{0}}

/-- Preserve semantic non-influence by checking the actual new mechanism.
Unlike the earlier-vertex specialization, this allows an unused ambient parent
edge from the ignored coordinate into the updated vertex. -/
theorem FiniteLatentSCM.withPrivateBooleanNoise_otherMechanismsIgnore_of_replacement
    (base : ExactModel S) (pivot node : Fin S.count) (noise : FiniteProbRecord Bool)
    (replacement : S.ParentValues pivot -> base.latent.Inputs pivot -> Bool -> S.Value pivot)
    (ignored : base.OtherMechanismsIgnore node)
    (replacementIgnores : pivot ≠ node ->
      forall (first second : S.ParentValues pivot) (inputs : base.latent.Inputs pivot) (bit : Bool),
        (forall parent (edge : S.directed parent pivot = true), parent ≠ node ->
          first parent edge = second parent edge) ->
        replacement first inputs bit = replacement second inputs bit) :
    (base.withPrivateBooleanNoise pivot noise replacement).OtherMechanismsIgnore node := by
  intro child childDifferent first second inputs agree
  by_cases updated : child = pivot
  · subst child
    rw [base.withPrivateBooleanNoise_mechanism_pivot,
      base.withPrivateBooleanNoise_mechanism_pivot]
    exact replacementIgnores childDifferent first second _ _ agree
  · rw [base.withPrivateBooleanNoise_mechanism_of_ne pivot noise replacement child updated,
      base.withPrivateBooleanNoise_mechanism_of_ne pivot noise replacement child updated]
    exact ignored child childDifferent first second _ agree

end Causality
end Thesis
