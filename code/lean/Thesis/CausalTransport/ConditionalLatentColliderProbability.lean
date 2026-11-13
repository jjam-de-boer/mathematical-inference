import Thesis.CausalTransport.ConditionalLatentCollider
import Thesis.Probability.ColliderRealization
import Thesis.Probability.FiniteProductReindex

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# The actual shared-latent collider realizes the finite posterior channel

The appended mask is shared by the two displayed observed mechanisms, and
the child's second appended source is private.  Their installed prior has
noise-first order.  Finite product reindexing puts that same prior in the
source-first order of `ColliderChannel`, including all mixed events.

The realization below is constructed from the proved prior encoding,
pointwise bit equations, and full-label context preservation.  No posterior
identity or conditional kernel gap is passed in as a hypothesis.  The common
probability layer then supplies evidence support, the actual normalized
posterior, full-event equality with the channel, and bias-dependent source-gap
reflection.  Each old source context retains its own normalizing mass.
-/

namespace ConditionalLatentCollider

def signal (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (child : Fin S.count) (intervention : (node : Fin S.count) -> Option (S.Value node)) : Event base.latent.Assignment :=
  fun old => hedgeIsSecond rich child (base.evalUnder intervention old child)

def evidence (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (noise : FiniteProbRecord Bool)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (context : Event S.Assignment) (value : Bool) : Event (model base rich parent child noise).latent.Assignment :=
  fun unit => context ((model base rich parent child noise).evalUnder intervention unit) &&
    decide (hedgeIsSecond rich child ((model base rich parent child noise).evalUnder intervention unit child) = value)

/-- The concrete record encoding for the real installed SCM.  Each field
is discharged by its structural or finite-product theorem.  In particular,
this is an inhabited realization, not an external channel assumption. -/
def realization (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (parent child : Fin S.count) (different : child ≠ parent) (noise : FiniteProbRecord Bool)
    (parentIgnored : base.OtherMechanismsIgnore parent) (childIgnored : base.OtherMechanismsIgnore child)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (parentFree : intervention parent = none) (childFree : intervention child = none)
    (nodes : NodeSet S) (context : Event S.Assignment) (localContext : EventDependsOnlyOn nodes context)
    (parentAway : nodes parent = false) (childAway : nodes child = false) (value : Bool) :
    ColliderChannel.Realization base.prior (signal base rich child intervention)
      (fun old => context (base.evalUnder intervention old)) noise value
      (model base rich parent child noise).prior (evidence base rich parent child noise intervention context value)
      (fun unit => hedgeIsSecond rich parent ((model base rich parent child noise).evalUnder intervention unit parent)) where
  encode := fun input => assignment base rich parent child noise input.2 input.1.2 input.1.1
  prior_probVal := fun event =>
    QProb.equiv_trans (prior_probVal base rich parent child noise event)
      (base.prior.product_cycle_probVal noise ColliderChannel.fairMask
        (fun input => event (assignment base rich parent child noise input.2 input.1.2 input.1.1)))
  evidence_encode := fun input => by
    unfold evidence
    have contextEqual : context ((model base rich parent child noise).evalUnder intervention
        (assignment base rich parent child noise input.2 input.1.2 input.1.1)) =
        context (base.evalUnder intervention input.1.1) := by
      apply localContext
      intro node selected
      have notParent : node ≠ parent := by
        intro same
        rw [same, parentAway] at selected
        cases selected
      have notChild : node ≠ child := by
        intro same
        rw [same, childAway] at selected
        cases selected
      exact evalUnder_of_away base rich parent child noise parentIgnored childIgnored
        intervention input.1.1 input.2 input.1.2 node notParent notChild
    rw [contextEqual, (bit_equations base rich parent child different noise parentIgnored childIgnored
      intervention parentFree childFree input.1.1 input.2 input.1.2).2]
    change (context (base.evalUnder intervention input.1.1) &&
      decide (Bool.xor (Bool.xor (signal base rich child intervention input.1.1) input.2) input.1.2 = value)) =
      (context (base.evalUnder intervention input.1.1) &&
      decide (Bool.xor (Bool.xor (signal base rich child intervention input.1.1) input.1.2) input.2 = value))
    cases signal base rich child intervention input.1.1 <;> cases input.2 <;> cases input.1.2 <;> rfl
  readout_encode := fun input =>
    (bit_equations base rich parent child different noise parentIgnored childIgnored
      intervention parentFree childFree input.1.1 input.2 input.1.2).1

end ConditionalLatentCollider
end Causality
end Thesis
