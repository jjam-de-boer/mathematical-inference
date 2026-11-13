import Thesis.CausalTransport.HedgeConditionalRoot
import Thesis.CausalTransport.ConditionalColliderContextCounterexample

namespace Thesis
namespace Causality

open Probability

/-!
# Positive original-query collider countermodels with any number of hedge roots

The root selector supplies a supported full-label conditional signal in the
positive carrier pair.  This module installs the incoming-parent collider at
that selected root while retaining all the other root labels as context.  The
conditioning set is the whole common-root set, not a singleton substituted
for it, and the original outcome may contain additional coordinates.

Two label presentations have different roles.  The base SCMs retain their
original carrier labels.  Only the installed readout reserves the selected
reference label for bit one.  The reference still carries the original
action values, so the source support, source separation, and resulting kernel
cell all concern the same intervention.  No gap of the modified kernel or
equality of its conditioning denominators is supplied to the constructor.

For the selected-root constructor, the queried parent must lie outside the
large forest and have a declared edge into that root.  The automatic wrapper
accepts a queried outside parent with incoming edges to every common root,
which guarantees that whichever separated root the finite search finds is
admissible.  A further finite-search wrapper allows a different queried
incoming parent at each root.  These are genuine geometric restrictions,
not consequences of an arbitrary exhausted IDC exchange search.  General
active-path composition and unrestricted conditional completeness remain
separate obligations.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S} {query : ConditionalKernelQuery S}

namespace HedgeConditionalRoot.Witness

/-- Turn an already constructed separated-root witness into a positive
counterexample for the complete original conditional query.  The source
models, their observational equality, the source supports and gap, and the
two pivot non-influence proofs are all derived internally from the hedge.
The caller supplies only the displayed original-query geometry and noise. -/
noncomputable def positiveConditionalCounterexampleWithNoise
    {w : HedgeWitness graph query.jointNumerator} {rich : ObservedSignature.ValueRich S}
    (selected : HedgeConditionalRoot.Witness w rich)
    (parent : Fin S.count) (parentSelected : query.outcome parent = true)
    (roots : w.roots = query.condition) (outside : w.large parent = false)
    (edge : S.directed parent selected.root = true)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query := by
  let left := w.largeCarrierDefectParityModel rich
  let right := w.smallCarrierDefectParityModel rich
  let readout := selected.readoutValues
  -- The outside parent and the common root have no kept forest child.  In
  -- these carrier SCMs this means every other mechanism ignores each pivot,
  -- exactly the non-influence needed to preserve the full observed law when
  -- the incoming-parent collider is installed.
  have childSelected : query.condition selected.root = true :=
    (congrFun roots selected.root).symm.trans selected.root_selected
  have parentNone := w.large_forest.child_off_set parent outside
  have childNone := ((w.large_forest.roots_exact selected.root).mp selected.root_selected).2
  -- The source pair keeps its original carrier labels.  The new readout
  -- presentation changes labels only away from the intervened coordinates,
  -- so this cell uses the same original action in both presentations.
  have interventionEq : query.operationKernel.intervention selected.reference = hedgeDoSecond rich query.action := by
    funext node
    cases active : query.action node with
    | false => simp only [ConditionalKernelQuery.operationKernel, Kernel.intervention, hedgeDoSecond, active, Bool.false_eq_true, if_false]
    | true => simp only [ConditionalKernelQuery.operationKernel, Kernel.intervention, hedgeDoSecond, active, if_true,
        selected.action_values node active]
  have contextEq (model : ExactModel S) :
      (fun old => Kernel.agreesOn (NodeSet.diff query.condition (NodeSet.singleton selected.root)) selected.reference
        (model.evalUnder (query.operationKernel.intervention selected.reference) old)) = selected.sourceContext model := by
    funext old
    rw [interventionEq]
    exact congrArg (fun nodes => Kernel.agreesOn (NodeSet.diff nodes (NodeSet.singleton selected.root)) selected.reference
      (model.evalUnder (hedgeDoSecond rich query.action) old)) roots.symm
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
  -- Transport the selected conditional gap, including its actual source
  -- context.  We do not replace it with a marginal child-bit gap or assert
  -- that the left and right conditioning masses are equal.
  have leftLaw : QProb.Equiv
      ((left.prior.conditionOn (fun old => Kernel.agreesOn (NodeSet.diff query.condition (NodeSet.singleton selected.root)) selected.reference
          (left.evalUnder (query.operationKernel.intervention selected.reference) old)) leftSupported).probVal
        (ConditionalCollider.signal left readout selected.root (query.operationKernel.intervention selected.reference)))
      ((left.prior.conditionOn (selected.sourceContext left) selected.left_source_supported).probVal
        (fun old => hedgeIsSecond readout selected.root (left.evalUnder (hedgeDoSecond rich query.action) old selected.root))) := by
    -- Conditioning carries its support proof in the record's type.  The
    -- simplifier transports that dependent proof with the event equality;
    -- rewriting the event alone would leave a proof of the old event.
    simp only [contextEq left]
    apply FiniteProbRecord.probVal_congr
    intro old
    unfold ConditionalCollider.signal
    rw [interventionEq]
  have rightLaw : QProb.Equiv
      ((right.prior.conditionOn (fun old => Kernel.agreesOn (NodeSet.diff query.condition (NodeSet.singleton selected.root)) selected.reference
          (right.evalUnder (query.operationKernel.intervention selected.reference) old)) rightSupported).probVal
        (ConditionalCollider.signal right readout selected.root (query.operationKernel.intervention selected.reference)))
      ((right.prior.conditionOn (selected.sourceContext right) selected.right_source_supported).probVal
        (fun old => hedgeIsSecond readout selected.root (right.evalUnder (hedgeDoSecond rich query.action) old selected.root))) := by
    simp only [contextEq right]
    apply FiniteProbRecord.probVal_congr
    intro old
    unfold ConditionalCollider.signal
    rw [interventionEq]
  exact ConditionalCollider.contextCounterexample query left right
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

/-! ## Finite incoming-parent selection after the source root is known -/

/-- The concrete parent data needed by the collider constructor at one root.
The parent is a queried outcome outside the large forest, and the declared
incoming edge belongs to the original observed signature. -/
structure IncomingParent (w : HedgeWitness graph query.jointNumerator) (root : Fin S.count) where
  node : Fin S.count
  selected : query.outcome node = true
  outside : w.large node = false
  edge : S.directed node root = true

/-- An entirely finite geometry test.  In particular, different roots may
pass this test at different queried parents; no shared parent is required. -/
def incomingParentTest (w : HedgeWitness graph query.jointNumerator)
    (root parent : Fin S.count) : Bool :=
  query.outcome parent && !w.large parent && S.directed parent root

/-- Return the first eligible queried parent in the established topological
order.  The data comes from the computed `find?` result.  The existence
characterization of `finAny` is used only to refute the impossible exhausted
branch, never to extract an observed node from a proposition. -/
def incomingParent (w : HedgeWitness graph query.jointNumerator) (root : Fin S.count)
    (available : finAny S.count (incomingParentTest w root) = true) : IncomingParent w root :=
  match found : (List.finRange S.count).find? (incomingParentTest w root) with
  | some parent =>
      let checked : incomingParentTest w root parent = true := List.find?_some found
      let passed := Bool.and_eq_true_iff.mp checked
      let first := Bool.and_eq_true_iff.mp passed.1
      { node := parent
        selected := first.1
        outside := by
          cases included : w.large parent with
          | false => rfl
          | true =>
              have impossible := first.2
              rw [included] at impossible
              cases impossible
        edge := passed.2 }
  | none => False.elim (by
      rcases (finAny_eq_true_iff (incomingParentTest w root)).mp available with ⟨parent, passed⟩
      exact ((List.find?_eq_none.mp found) parent (List.mem_finRange parent)) passed)

end HedgeConditionalRoot

/-- Automatically select a separated root when a queried outside parent has
a declared edge into every common root.  No root count, binary-alphabet,
singleton-outcome, chosen reference, or hand-supplied source-gap restriction
is imposed.  The entire original root conditioner is retained. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootColliderWithNoise
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (parent : Fin S.count) (parentSelected : query.outcome parent = true)
    (roots : w.roots = query.condition) (outside : w.large parent = false)
    (parentEdges : forall root, w.roots root = true -> S.directed parent root = true)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  let selected := w.conditionedRoot rich
  selected.positiveConditionalCounterexampleWithNoise parent parentSelected roots outside
    (parentEdges selected.root selected.root_selected) noise noisePositive gap positiveGap bias

/-- The automatic multi-root constructor with the explicit supported `2:1`
stay/flip noise.  It chooses neither a positive epsilon nor a noise model
from an existential proposition. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootCollider
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (parent : Fin S.count) (parentSelected : query.outcome parent = true)
    (roots : w.roots = query.condition) (outside : w.large parent = false)
    (parentEdges : forall root, w.roots root = true -> S.directed parent root = true) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  w.positiveConditionalCounterexampleOfRootColliderWithNoise rich parent parentSelected roots outside parentEdges
    (FiniteProbRecord.biasedFlip 1 1 (by decide)) (by intro bit; cases bit <;> decide +kernel)
    1 (by decide) (by decide +kernel)

/-- Select the separated root first, then search its own queried incoming
parent.  Every common root is required to have an eligible parent, but that
parent need not be the same node across roots.  The Boolean availability
premise is a graph test, not a source-law gap or a conditional countermodel
assumption.  The actual root, reference, context support, and semantic gap
continue to come from the arbitrary-hedge conditional selector. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootSpecificParentsWithNoise
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (roots : w.roots = query.condition)
    (parentsAvailable : forall root, w.roots root = true ->
      finAny S.count (HedgeConditionalRoot.incomingParentTest w root) = true)
    (noise : FiniteProbRecord Bool)
    (noisePositive : forall bit, noise.EventPositive (FiniteProbRecord.singletonEvent bit))
    (gap : Nat) (positiveGap : 0 < gap)
    (bias : FiniteProbRecord.eventMass noise.atoms (fun bit => !bit) =
      FiniteProbRecord.eventMass noise.atoms id + gap) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  let selected := w.conditionedRoot rich
  let parent := HedgeConditionalRoot.incomingParent w selected.root
    (parentsAvailable selected.root selected.root_selected)
  selected.positiveConditionalCounterexampleWithNoise parent.node parent.selected roots parent.outside parent.edge
    noise noisePositive gap positiveGap bias

/-- The root-specific incoming-parent constructor with explicit supported
`2:1` stay/flip noise.  Neither the parent data nor the noise model is chosen
by a choice principle. -/
noncomputable def HedgeWitness.positiveConditionalCounterexampleOfRootSpecificParents
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (roots : w.roots = query.condition)
    (parentsAvailable : forall root, w.roots root = true ->
      finAny S.count (HedgeConditionalRoot.incomingParentTest w root) = true) :
    ConditionalCounterexampleIn (GraphModelClass.positive graph) query :=
  w.positiveConditionalCounterexampleOfRootSpecificParentsWithNoise rich roots parentsAvailable
    (FiniteProbRecord.biasedFlip 1 1 (by decide)) (by intro bit; cases bit <;> decide +kernel)
    1 (by decide) (by decide +kernel)

end Causality
end Thesis
