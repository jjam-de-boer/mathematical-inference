import Thesis.CausalTransport.HedgeConditionalLatentColliderRoute

namespace Thesis
namespace Causality

open Probability

/-!
# Root-specific observed or shared-latent collider entries

Conditional uniqueness selects a separated common root from the actual hedge
carrier pair.  That root may have an observed-parent entry or a shared-latent
entry followed by a directed route to an original outcome.  Requiring every
root to have the same kind is unnecessary: the finite eligibility test here
permits either kind at each root independently.

The selected root is not chosen for convenient geometry.  Its existing
semantic gap is retained, and only then is its own entry test evaluated.
Observed entry is used when available; otherwise the proved Boolean
disjunction supplies shared-latent entry.  Both branches construct their own
actual source pair and directed-tail readiness from the original hedge.
Neither a pointwise countermodel family nor an existentially chosen entry
kind is supplied by the caller.

The first edge can vary between roots, but every subsequent edge is still
directed and every tail destination avoids the action and large forest.
All common roots must still be precisely the original conditioner.  This
combines the two covered entry families; it does not silently turn them into
a construction for arbitrary collider-rich active paths.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S}
  {query : ConditionalKernelQuery S}

namespace HedgeConditionalRoot

/-- Either checked entry kind may carry this root's source signal to an
original outcome.  Each kind includes its own finite parent and directed-tail
search, so this disjunction is graph data rather than a semantic promise. -/
def colliderEntryRouteAvailable (w : HedgeWitness graph query.jointNumerator)
    (root : Fin S.count) : Bool :=
  NodeSet.meetsBool NodeSet.full (incomingRouteParentMask w root) ||
    NodeSet.meetsBool NodeSet.full (sharedLatentRouteParentMask w root)

namespace Witness

/-- Keep the already selected separated root and construct whichever
checked entry it admits.  The Boolean case split is constructive; it neither
uses propositional excluded middle nor chooses an SCM from an existence proof. -/
noncomputable def positiveConditionalCounterexampleOfColliderEntryWithNoise
    {w : HedgeWitness graph query.jointNumerator} {rich : ObservedSignature.ValueRich S}
    (selected : HedgeConditionalRoot.Witness w rich)
    (roots : w.roots = query.condition)
    (available : colliderEntryRouteAvailable w selected.root = true)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  cases observed : NodeSet.meetsBool NodeSet.full (incomingRouteParentMask w selected.root) with
  | true =>
      let geometry := incomingRoute w roots selected.root observed
      exact selected.positiveConditionalCounterexampleAlongRouteWithNoise roots geometry.parent geometry.endpoint
        geometry.outside geometry.parent_unacted geometry.edge geometry.route geometry.endpoint_selected
        geometry.destinations_unacted geometry.destinations_ungiven geometry.destinations_sinks
        noise noisePositive gap positiveGap bias (fun _ => noise) (fun _ _ => noisePositive)
        (fun _ => gap) (fun _ _ => positiveGap) (fun _ _ => bias)
  | false =>
      have shared : NodeSet.meetsBool NodeSet.full (sharedLatentRouteParentMask w selected.root) = true := by
        simpa only [colliderEntryRouteAvailable, observed, Bool.false_or] using available
      let geometry := sharedLatentIncomingRoute w roots selected.root shared
      exact selected.positiveConditionalCounterexampleAlongSharedLatentRouteWithNoise roots geometry.parent geometry.endpoint
        geometry.outside geometry.parent_unacted geometry.edge geometry.route geometry.endpoint_selected
        geometry.destinations_unacted geometry.destinations_ungiven geometry.destinations_sinks
        noise noisePositive gap positiveGap bias (fun _ => noise) (fun _ _ => noisePositive)
        (fun _ => gap) (fun _ _ => positiveGap) (fun _ _ => bias)

end Witness
end HedgeConditionalRoot

/-- Select the genuine separated root internally and use that root's own
checked collider entry and directed tail.  Roots may have different entry
kinds, auxiliary vertices, original endpoints and route lengths. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootSpecificColliderEntriesWithNoise
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (roots : w.roots = query.condition)
    (entriesAvailable : forall root, w.roots root = true ->
      HedgeConditionalRoot.colliderEntryRouteAvailable w root = true)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  let selected := w.conditionedRoot rich
  selected.positiveConditionalCounterexampleOfColliderEntryWithNoise roots
    (entriesAvailable selected.root selected.root_selected) noise noisePositive gap positiveGap bias

/-- Explicit supported `2:1` noise in either entry branch and throughout
its directed tail.  The full original action, conditioner and outcome are
preserved, including labels outside the two distinguished readout bits. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootSpecificColliderEntries
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (roots : w.roots = query.condition)
    (entriesAvailable : forall root, w.roots root = true ->
      HedgeConditionalRoot.colliderEntryRouteAvailable w root = true) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  w.positiveConditionalCounterexampleOfRootSpecificColliderEntriesWithNoise rich roots entriesAvailable
    (FiniteProbRecord.biasedFlip 1 1 (by decide)) (by intro bit; cases bit <;> decide +kernel)
    1 (by decide) (by decide +kernel)

end Causality
end Thesis
