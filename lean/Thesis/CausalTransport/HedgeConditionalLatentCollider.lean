import Thesis.CausalTransport.HedgeConditionalRoot
import Thesis.CausalTransport.ConditionalLatentColliderCounterexample

namespace Thesis
namespace Causality

open Probability

/-!
# Positive hedge countermodels through an existing shared latent pair

The incoming-parent collider construction uses an observed arrow into the
selected conditioned root.  A back-door path can instead begin at a latent
pair.  Here the queried readout and selected root share a fresh fair mask on
an already declared bidirected edge, so the projected graph is unchanged.
No observed arrow between those pivots is required or silently introduced.

The arbitrary-hedge root selector supplies the source models, a supported
full-label context, and a genuinely separated root conditional.  The bridge
below transports that data at the original action values and installs the
shared-latent construction.  Both SCMs remain positive on the whole observed
alphabet, and the entire observational law is preserved.  Additional queried
outcomes are retained by conditional marginalization, not discarded.

The root conditioner must still equal the common-root set, and the selected
root needs a queried bidirected neighbour outside the large forest.  The
finite-search wrapper allows a different eligible neighbour at each root.
These are checked geometric restrictions, not consequences of every exhausted
IDC exchange search.  Arbitrary active-path composition and unrestricted
conditional terminal countermodels remain separate semantic obligations.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S}
  {query : ConditionalKernelQuery S}

namespace HedgeConditionalRoot.Witness

/-- Install the shared-latent collider at an already selected separated root.
All source-gap, support, observational-equality and non-influence data come
from the actual hedge carrier pair.  Only original-query geometry and the
explicit supported biased noise are supplied by the caller. -/
noncomputable def positiveConditionalCounterexampleWithSharedLatentNoise
    {w : HedgeWitness graph query.jointNumerator} {rich : ObservedSignature.ValueRich S}
    (selected : HedgeConditionalRoot.Witness w rich)
    (parent : Fin S.count) (parentSelected : query.outcome parent = true)
    (roots : w.roots = query.condition) (outside : w.large parent = false)
    (edge : graph.bidirected parent selected.root = true)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  let left := w.largeCarrierDefectParityModel rich
  let right := w.smallCarrierDefectParityModel rich
  let readout := selected.readoutValues
  -- A common root has no kept child; an outside vertex is not a kept forest
  -- parent either.  Thus both base pivots satisfy exactly the non-influence
  -- required by the shared-mask and private-restoration evaluations.
  have childSelected : query.condition selected.root = true :=
    (congrFun roots selected.root).symm.trans selected.root_selected
  have parentNone := w.large_forest.child_off_set parent outside
  have childNone := ((w.large_forest.roots_exact selected.root).mp selected.root_selected).2
  -- The new readout reserves the selected reference label for its true bit.
  -- Its action coordinates, however, are the old action coordinates.  The
  -- source conditional and final kernel therefore concern one intervention.
  have interventionEq : query.operationKernel.intervention selected.reference =
      hedgeDoSecond rich query.action := by
    funext node
    cases active : query.action node with
    | false => simp only [ConditionalKernelQuery.operationKernel, Kernel.intervention,
        hedgeDoSecond, active, Bool.false_eq_true, if_false]
    | true => simp only [ConditionalKernelQuery.operationKernel, Kernel.intervention,
        hedgeDoSecond, active, if_true, selected.action_values node active]
  have contextEq (model : ExactModel S) :
      (fun old => Kernel.agreesOn (NodeSet.diff query.condition (NodeSet.singleton selected.root))
        selected.reference (model.evalUnder (query.operationKernel.intervention selected.reference) old)) =
      selected.sourceContext model := by
    funext old
    rw [interventionEq]
    exact congrArg (fun nodes => Kernel.agreesOn (NodeSet.diff nodes (NodeSet.singleton selected.root))
      selected.reference (model.evalUnder (hedgeDoSecond rich query.action) old)) roots.symm
  have leftSupported : left.prior.EventPositive (fun old =>
      Kernel.agreesOn (NodeSet.diff query.condition (NodeSet.singleton selected.root)) selected.reference
        (left.evalUnder (query.operationKernel.intervention selected.reference) old)) := by
    rw [contextEq left]
    exact selected.left_source_supported
  have rightSupported : right.prior.EventPositive (fun old =>
      Kernel.agreesOn (NodeSet.diff query.condition (NodeSet.singleton selected.root)) selected.reference
        (right.evalUnder (query.operationKernel.intervention selected.reference) old)) := by
    rw [contextEq right]
    exact selected.right_source_supported
  -- Compare the actual conditioned priors.  Their context denominators need
  -- not agree, and a marginal root gap cannot replace this conditional gap.
  have leftLaw : QProb.Equiv
      ((left.prior.conditionOn (fun old => Kernel.agreesOn
          (NodeSet.diff query.condition (NodeSet.singleton selected.root)) selected.reference
          (left.evalUnder (query.operationKernel.intervention selected.reference) old)) leftSupported).probVal
        (ConditionalLatentCollider.signal left readout selected.root
          (query.operationKernel.intervention selected.reference)))
      ((left.prior.conditionOn (selected.sourceContext left) selected.left_source_supported).probVal
        (fun old => hedgeIsSecond readout selected.root
          (left.evalUnder (hedgeDoSecond rich query.action) old selected.root))) := by
    -- Transport the dependent support proof together with its event.
    simp only [contextEq left]
    apply FiniteProbRecord.probVal_congr
    intro old
    unfold ConditionalLatentCollider.signal
    rw [interventionEq]
  have rightLaw : QProb.Equiv
      ((right.prior.conditionOn (fun old => Kernel.agreesOn
          (NodeSet.diff query.condition (NodeSet.singleton selected.root)) selected.reference
          (right.evalUnder (query.operationKernel.intervention selected.reference) old)) rightSupported).probVal
        (ConditionalLatentCollider.signal right readout selected.root
          (query.operationKernel.intervention selected.reference)))
      ((right.prior.conditionOn (selected.sourceContext right) selected.right_source_supported).probVal
        (fun old => hedgeIsSecond readout selected.root
          (right.evalUnder (hedgeDoSecond rich query.action) old selected.root))) := by
    simp only [contextEq right]
    apply FiniteProbRecord.probVal_congr
    intro old
    unfold ConditionalLatentCollider.signal
    rw [interventionEq]
  exact ConditionalLatentCollider.contextCounterexample query left right
    (w.largeCarrierDefectParityModel_compatible rich) (w.smallCarrierDefectParityModel_compatible rich)
    (w.largeCarrierDefectParityModel_positive rich) (w.smallCarrierDefectParityModel_positive rich)
    (w.carrierDefectParityModels_observationally_equivalent rich) readout parent selected.root edge parentSelected childSelected
    (w.largeCarrierDefectParityModel_otherMechanismsIgnore rich parent parentNone)
    (w.smallCarrierDefectParityModel_otherMechanismsIgnore rich parent parentNone)
    (w.largeCarrierDefectParityModel_otherMechanismsIgnore rich selected.root childNone)
    (w.smallCarrierDefectParityModel_otherMechanismsIgnore rich selected.root childNone)
    noise noisePositive gap positiveGap bias selected.reference rfl rfl leftSupported rightSupported
    (fun equivalent => selected.source_readout_separated
      (QProb.equiv_trans (QProb.equiv_symm leftLaw) (QProb.equiv_trans equivalent rightLaw)))

end HedgeConditionalRoot.Witness

namespace HedgeConditionalRoot

/-! ## Constructive root-specific shared-parent selection -/

/-- An eligible shared-latent readout for a single root.  `parent` names its
role in the collider channel; the graph relation is bidirected, not an
observed parental arrow.  The two roles must not be confused. -/
structure SharedLatentParent (w : HedgeWitness graph query.jointNumerator) (root : Fin S.count) where
  node : Fin S.count
  selected : query.outcome node = true
  outside : w.large node = false
  edge : graph.bidirected node root = true

/-- The graph-only eligibility mask for the shared-latent readout.  Query
membership is tested separately by `NodeSet.meetsBool`, so the established
constructive meeting selector can return an actual observed node. -/
def sharedLatentParentMask (w : HedgeWitness graph query.jointNumerator) (root : Fin S.count) : NodeSet S :=
  fun node => !w.large node && graph.bidirected node root

/-- Select a queried outside neighbour from the computed finite meeting.
No node is chosen by eliminating a propositional existence proof. -/
def sharedLatentParent (w : HedgeWitness graph query.jointNumerator) (root : Fin S.count)
    (available : NodeSet.meetsBool query.outcome (sharedLatentParentMask w root) = true) :
    SharedLatentParent w root := by
  let node := NodeSet.getMeeting query.outcome (sharedLatentParentMask w root) available
  have passed := Bool.and_eq_true_iff.mp (NodeSet.getMeeting_right available)
  refine ⟨node, NodeSet.getMeeting_left available, ?_, passed.2⟩
  cases included : w.large node with
  | false => rfl
  | true =>
      have impossible := passed.1
      rw [included] at impossible
      cases impossible

end HedgeConditionalRoot

/-- Select the genuinely separated hedge root first, then its own queried
shared-latent neighbour.  Eligible neighbours can differ across roots.  The
only universal premise is a finite graph availability test, not a semantic
gap or an assumed counterexample family. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootSpecificLatentParentsWithNoise
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (roots : w.roots = query.condition)
    (parentsAvailable : forall root, w.roots root = true ->
      NodeSet.meetsBool query.outcome (HedgeConditionalRoot.sharedLatentParentMask w root) = true)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  let selected := w.conditionedRoot rich
  let parent := HedgeConditionalRoot.sharedLatentParent w selected.root
    (parentsAvailable selected.root selected.root_selected)
  selected.positiveConditionalCounterexampleWithSharedLatentNoise parent.node parent.selected roots parent.outside parent.edge
    noise noisePositive gap positiveGap bias

/-- Root-specific shared-latent countermodels with the explicit supported
`2:1` stay/flip noise.  Both the neighbour and the noise are concrete finite
data, rather than choices from existential mathematical statements. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootSpecificLatentParents
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (roots : w.roots = query.condition)
    (parentsAvailable : forall root, w.roots root = true ->
      NodeSet.meetsBool query.outcome (HedgeConditionalRoot.sharedLatentParentMask w root) = true) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  w.positiveConditionalCounterexampleOfRootSpecificLatentParentsWithNoise rich roots parentsAvailable
    (FiniteProbRecord.biasedFlip 1 1 (by decide)) (by intro bit; cases bit <;> decide +kernel)
    1 (by decide) (by decide +kernel)

end Causality
end Thesis
