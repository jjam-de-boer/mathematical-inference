import Thesis.CausalTransport.Completeness

namespace Thesis
namespace Causality

open Probability

/-!
# Semantic support of the hedge outcome-flow models

`Completeness` constructs two graph-compatible additive flows that transport
hedge incidence to a common set of query-outcome sinks and proves that their
interventional kernels disagree.  This module develops the complementary
observational-support calculation.

The large and small flows do not impose the same pair-root equations at a
readout vertex in `large \ small`: the large flow injects outer incidence,
whereas the small flow deliberately injects zero so that its sink parity
stays even.  The definitions below expose that distinction rather than hiding
it in an opaque probability argument.  They prove exact finite support
characterizations for both models, then recover observational equivalence
under the geometrically natural condition that every readout vertex lying in
`large` already lies in `small`.  Under that condition the two support fibers
have equal cardinality, yielding an unrestricted counterexample for the
original query.

Everything is finite and executable.  Pair-root witnesses are counted by
explicit enumerations, Boolean target predicates replace proposition-level
case splits, and no choice principle or excluded middle is used.
-/

/-! ## Exact support of a routed parity model -/

/--
Test that every routed vertex outside the designated source set has zero
required incidence in `target`.  This is the side condition that rules out
an impossible source-free parity equation while remaining computational.
-/
def hedgeFlowZeroSourceOutside (rich : ObservedSignature.ValueRich S)
    (flowNodes sourceNodes : NodeSet S) (successor : ForestChild S)
    (target : S.Assignment) : Bool :=
  (NodeSet.members flowNodes).all fun child =>
    if sourceNodes child then true
    else hedgeForestRequiredIncidence rich successor target child == false

/-- Prove the executable zero-source test by checking each routed vertex. -/
theorem hedgeFlowZeroSourceOutside_of
    (rich : ObservedSignature.ValueRich S)
    (flowNodes sourceNodes : NodeSet S) (successor : ForestChild S)
    (target : S.Assignment)
    (zero : forall child, flowNodes child = true →
      sourceNodes child = false →
      hedgeForestRequiredIncidence rich successor target child = false) :
    hedgeFlowZeroSourceOutside rich flowNodes sourceNodes successor target =
      true := by
  unfold hedgeFlowZeroSourceOutside
  apply List.all_eq_true.mpr
  intro child member
  have selected := (NodeSet.mem_members_iff flowNodes child).mp member
  cases source : sourceNodes child with
  | true => simp
  | false =>
      simp [zero child selected source]

/-- Recover the pointwise zero-source equation from the executable test. -/
theorem hedgeFlowZeroSourceOutside_spec
    (rich : ObservedSignature.ValueRich S)
    (flowNodes sourceNodes : NodeSet S) (successor : ForestChild S)
    (target : S.Assignment)
    (valid :
      hedgeFlowZeroSourceOutside rich flowNodes sourceNodes successor target =
        true) :
    forall child, flowNodes child = true → sourceNodes child = false →
      hedgeForestRequiredIncidence rich successor target child = false := by
  intro child selected source
  have member := (NodeSet.mem_members_iff flowNodes child).mpr selected
  have tested := (List.all_eq_true.mp valid) child member
  simp [source] at tested
  exact tested

/-- Every evaluation of a readout-flow model uses only its two parity values. -/
theorem hedgeFlowReadoutModel_eval_valid
    (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (successor : ForestChild S)
    (base : ExactModel S)
    (sourceBit : forall child, S.ParentValues child →
      base.latent.Inputs child → Bool)
    (u : base.latent.Assignment) :
    hedgeParityTargetValid rich nodes
      ((hedgeFlowReadoutModel rich nodes successor base sourceBit).eval u) =
        true := by
  apply hedgeParityTargetValid_of
  intro child inside
  change
    (hedgeFlowReadoutModel rich nodes successor base sourceBit).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child = rich.first child ∨
      (hedgeFlowReadoutModel rich nodes successor base sourceBit).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child = rich.second child
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
  simp only [hedgeFlowReadoutModel, inside, if_true]
  unfold hedgeParityValue
  split <;> simp

/--
The pair-root coordinates of a large-flow latent assignment realize exactly
the incidences required by its observable output.
-/
theorem HedgeWitness.largeOutcomeFlowModel_pairBitsRealizes_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgePairBitsRealizes G w.large
        (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor
          ((w.largeOutcomeFlowModel rich).eval u))
        (hedgePairBitsOf G u) = true := by
  apply hedgePairBitsRealizes_of
  intro child inLarge
  have selected : w.largeOutcomeFlowNodes child = true := by
    simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union, inLarge]
  have equation := hedgeFlowReadoutModel_evalNodeUnder_bit rich
    w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
    w.largeOutcomeFlowSuccessor_wellFormed (w.largeParityModel rich)
    (hedgeForestIncidenceSource G w.large)
    (FiniteLatentSCM.noIntervention S) u child selected rfl
  simp only [hedgeForestIncidenceSource, inLarge, if_true] at equation
  have equation' :
      hedgeIsSecond rich child ((w.largeOutcomeFlowModel rich).eval u child) =
        Bool.xor
          (hedgeXorPairBitsWithin G w.large child (fun latent _ => u latent))
          (hedgeRoutingIncomingBits w.largeOutcomeFlowSuccessor (fun parent =>
            hedgeIsSecond rich parent
              ((w.largeOutcomeFlowModel rich).eval u parent)) child) := by
    simpa only [FiniteLatentSCM.eval,
      HedgeWitness.largeOutcomeFlowModel] using equation
  rw [← hedgeForestParentBitsFrom_eq_routingIncomingBits rich
    w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
    w.largeOutcomeFlowSuccessor_wellFormed
    ((w.largeOutcomeFlowModel rich).eval u) child] at equation'
  rw [← hedgeXorPairBitsWithin_pairBitsOf G w.large u child]
  unfold hedgeForestRequiredIncidence
  rw [equation']
  generalize
    hedgeXorPairBitsWithin G w.large child (fun latent _ => u latent) = pair
  generalize hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child
    (fun parent _ => (w.largeOutcomeFlowModel rich).eval u parent) = incoming
  cases pair <;> cases incoming <;> rfl

/-- A large-flow evaluation satisfies every source-free routing equation. -/
theorem HedgeWitness.largeOutcomeFlowModel_zeroSourceOutside_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeFlowZeroSourceOutside rich w.largeOutcomeFlowNodes w.large
      w.largeOutcomeFlowSuccessor ((w.largeOutcomeFlowModel rich).eval u) =
        true := by
  apply hedgeFlowZeroSourceOutside_of
  intro child selected outside
  have equation := hedgeFlowReadoutModel_evalNodeUnder_bit rich
    w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
    w.largeOutcomeFlowSuccessor_wellFormed (w.largeParityModel rich)
    (hedgeForestIncidenceSource G w.large)
    (FiniteLatentSCM.noIntervention S) u child selected rfl
  simp only [hedgeForestIncidenceSource, outside] at equation
  have equation' :
      hedgeIsSecond rich child ((w.largeOutcomeFlowModel rich).eval u child) =
        Bool.xor false
          (hedgeRoutingIncomingBits w.largeOutcomeFlowSuccessor (fun parent =>
            hedgeIsSecond rich parent
              ((w.largeOutcomeFlowModel rich).eval u parent)) child) := by
    simpa only [FiniteLatentSCM.eval,
      HedgeWitness.largeOutcomeFlowModel] using equation
  rw [← hedgeForestParentBitsFrom_eq_routingIncomingBits rich
    w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
    w.largeOutcomeFlowSuccessor_wellFormed
    ((w.largeOutcomeFlowModel rich).eval u) child] at equation'
  unfold hedgeForestRequiredIncidence
  rw [equation']
  generalize hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child
    (fun parent _ => (w.largeOutcomeFlowModel rich).eval u parent) = incoming
  cases incoming <;> rfl

/--
Outside the routed large flow, evaluation preserves the private latent
coordinate selected for each observed vertex.
-/
theorem HedgeWitness.largeOutcomeFlowModel_privateCoordinatesFit_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgePrivateCoordinatesFit w.largeOutcomeFlowNodes
      ((w.largeOutcomeFlowModel rich).eval u)
      (hedgePrivateCoordinatesOf G u) = true := by
  apply hedgePrivateCoordinatesFit_of
  intro child outside
  have outsideLarge : w.large child = false := by
    cases inLarge : w.large child with
    | false => rfl
    | true =>
        simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union, inLarge] at outside
  change hedgePrivateIndex G child (fun root _ => u root) =
    hedgeIndexOfValue S child ((w.largeOutcomeFlowModel rich).eval u child)
  have outputEq :
      (w.largeOutcomeFlowModel rich).eval u child =
        hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun root _ => u root)) := by
    change
      (w.largeOutcomeFlowModel rich).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child = _
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    simp [HedgeWitness.largeOutcomeFlowModel, hedgeFlowReadoutModel, outside,
      HedgeWitness.largeParityModel, hedgeForestParityModel,
      hedgeForestParityOutput, outsideLarge]
  have indexed := congrArg (hedgeIndexOfValue S child) outputEq
  rw [hedgeIndexOf_decode] at indexed
  exact indexed.symm

/--
Reconstruct one coordinate of a large-flow evaluation from its pair-root and
private-coordinate support constraints.
-/
theorem HedgeWitness.largeOutcomeFlowModel_evalNode_eq_of_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich w.largeOutcomeFlowNodes target = true)
    (zero : hedgeFlowZeroSourceOutside rich w.largeOutcomeFlowNodes w.large
      w.largeOutcomeFlowSuccessor target = true)
    (u : (hedgeLatentExtension G).Assignment)
    (realizes : hedgePairBitsRealizes G w.large
      (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor target)
      (hedgePairBitsOf G u) = true)
    (privateFits : hedgePrivateCoordinatesFit w.largeOutcomeFlowNodes target
      (hedgePrivateCoordinatesOf G u) = true)
    (child : Fin S.count) :
    (w.largeOutcomeFlowModel rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child = target child := by
  cases inside : w.largeOutcomeFlowNodes child with
  | false =>
      have outsideLarge : w.large child = false := by
        cases inLarge : w.large child with
        | false => rfl
        | true =>
            simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
              inLarge] at inside
      have privateAt := hedgePrivateCoordinatesFit_spec
        w.largeOutcomeFlowNodes target (hedgePrivateCoordinatesOf G u)
        privateFits child inside
      change hedgePrivateIndex G child (fun root _ => u root) =
        hedgeIndexOfValue S child (target child) at privateAt
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      simp only [HedgeWitness.largeOutcomeFlowModel, hedgeFlowReadoutModel,
        inside, Bool.false_eq_true, ↓reduceIte,
        HedgeWitness.largeParityModel, hedgeForestParityModel]
      simp [hedgeForestParityOutput, outsideLarge, privateAt,
        hedgePrivateDecode_index]
  | true =>
      have sourceEq :
          (if w.large child then
              hedgeXorPairBitsWithin G w.large child
                (fun latent _ => u latent)
            else false) =
            hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor
              target child := by
        cases inLarge : w.large child with
        | true =>
            simp only [if_true]
            rw [hedgeXorPairBitsWithin_pairBitsOf]
            exact hedgePairBitsRealizes_spec G w.large
              (hedgeForestRequiredIncidence rich
                w.largeOutcomeFlowSuccessor target)
              (hedgePairBitsOf G u) realizes child inLarge
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact (hedgeFlowZeroSourceOutside_spec rich
              w.largeOutcomeFlowNodes w.large w.largeOutcomeFlowSuccessor
              target zero child inside inLarge).symm
      have parents :
          hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child
              (fun parent _ =>
                (w.largeOutcomeFlowModel rich).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent) =
            hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child
              (fun parent _ => target parent) := by
        apply hedgeForestParentBitsFrom_congr rich child
        · intro _parent
          rfl
        · intro parent edge
          exact w.largeOutcomeFlowModel_evalNode_eq_of_support rich target
            valid zero u realizes privateFits parent
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      simp only [HedgeWitness.largeOutcomeFlowModel, hedgeFlowReadoutModel,
        inside, if_true, hedgeForestIncidenceSource]
      unfold HedgeWitness.largeOutcomeFlowModel at parents
      simp only [HedgeWitness.largeParityModel, hedgeForestParityModel] at sourceEq parents ⊢
      unfold hedgeFlowReadoutModel FiniteLatentSCM.noIntervention at parents
      simp only [hedgeForestIncidenceSource] at parents
      rw [sourceEq, parents]
      unfold hedgeForestRequiredIncidence
      rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      exact hedgeParityValue_isSecond_of_valid rich child (target child)
        (hedgeParityTargetValid_spec rich w.largeOutcomeFlowNodes target
          valid child inside)
termination_by child.val
decreasing_by
  exact S.directed_earlier edge

/-- Reconstruct the complete large-flow output from its support constraints. -/
theorem HedgeWitness.largeOutcomeFlowModel_eval_eq_of_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich w.largeOutcomeFlowNodes target = true)
    (zero : hedgeFlowZeroSourceOutside rich w.largeOutcomeFlowNodes w.large
      w.largeOutcomeFlowSuccessor target = true)
    (u : (hedgeLatentExtension G).Assignment)
    (realizes : hedgePairBitsRealizes G w.large
      (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor target)
      (hedgePairBitsOf G u) = true)
    (privateFits : hedgePrivateCoordinatesFit w.largeOutcomeFlowNodes target
      (hedgePrivateCoordinatesOf G u) = true) :
    (w.largeOutcomeFlowModel rich).eval u = target := by
  funext child
  exact w.largeOutcomeFlowModel_evalNode_eq_of_support rich target valid zero
    u realizes privateFits child

/--
Exact support theorem for the large outcome-flow model: a latent assignment
evaluates to `target` precisely when it belongs to the explicit coordinate
fiber determined by `target`.
-/
theorem HedgeWitness.largeOutcomeFlowModel_eval_mem_coordinateSupport_iff
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich w.largeOutcomeFlowNodes target = true)
    (zero : hedgeFlowZeroSourceOutside rich w.largeOutcomeFlowNodes w.large
      w.largeOutcomeFlowSuccessor target = true)
    (u : (hedgeLatentExtension G).Assignment) :
    (w.largeOutcomeFlowModel rich).eval u = target ↔
      u ∈ hedgeCoordinateSupportLatents G w.largeOutcomeFlowNodes target
        (hedgePairBitsRealizes G w.large
          (hedgeForestRequiredIncidence rich
            w.largeOutcomeFlowSuccessor target)) := by
  rw [hedgeCoordinateSupportLatents_mem_iff]
  constructor
  · intro evaluates
    subst target
    exact ⟨w.largeOutcomeFlowModel_pairBitsRealizes_eval rich u,
      w.largeOutcomeFlowModel_privateCoordinatesFit_eval rich u⟩
  · intro support
    exact w.largeOutcomeFlowModel_eval_eq_of_support rich target valid zero u
      support.1 support.2

/-! ## Exact support of the small routed model -/

/--
Pair-root constraints for the small outcome flow.  Vertices in `small` use
the small routed incidence; ordinary vertices of `large \ small` retain the
large-forest equation; readout vertices in `large \ small` impose no pair
equation because the small model injects zero there.
-/
def HedgeWitness.smallOutcomePairBitsRealizes
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (pairBits : Fin (pairRootCount G) → Bool) : Bool :=
  (NodeSet.members w.large).all fun child =>
    if w.small child then
      hedgeXorPairBitsWithinFrom G w.small child pairBits ==
        hedgeForestRequiredIncidence rich w.smallOutcomeFlowSuccessor
          target child
    else if w.rootReadoutNodes child then
      true
    else
      hedgeXorPairBitsWithinFrom G w.large child pairBits ==
        hedgeForestRequiredIncidence rich w.child target child

/-- Establish the small-flow pair constraints from their two active cases. -/
theorem HedgeWitness.smallOutcomePairBitsRealizes_of
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (pairBits : Fin (pairRootCount G) → Bool)
    (agreesSmall : forall child, w.small child = true →
      hedgeXorPairBitsWithinFrom G w.small child pairBits =
        hedgeForestRequiredIncidence rich w.smallOutcomeFlowSuccessor
          target child)
    (agreesOuter : forall child, w.large child = true →
      w.small child = false → w.rootReadoutNodes child = false →
      hedgeXorPairBitsWithinFrom G w.large child pairBits =
        hedgeForestRequiredIncidence rich w.child target child) :
    w.smallOutcomePairBitsRealizes rich target pairBits = true := by
  unfold HedgeWitness.smallOutcomePairBitsRealizes
  apply List.all_eq_true.mpr
  intro child member
  have inLarge := (NodeSet.mem_members_iff w.large child).mp member
  cases inSmall : w.small child with
  | true => simp [agreesSmall child inSmall]
  | false =>
      cases inReadout : w.rootReadoutNodes child with
      | true => simp
      | false =>
          simp [agreesOuter child inLarge inSmall inReadout]

/-- Extract the routed small-forest equation at a vertex of `small`. -/
theorem HedgeWitness.smallOutcomePairBitsRealizes_small
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (pairBits : Fin (pairRootCount G) → Bool)
    (realizes : w.smallOutcomePairBitsRealizes rich target pairBits = true)
    (child : Fin S.count) (inSmall : w.small child = true) :
    hedgeXorPairBitsWithinFrom G w.small child pairBits =
      hedgeForestRequiredIncidence rich w.smallOutcomeFlowSuccessor
        target child := by
  have inLarge := w.small_subset_large child inSmall
  have member := (NodeSet.mem_members_iff w.large child).mpr inLarge
  have tested := (List.all_eq_true.mp realizes) child member
  simp [inSmall] at tested
  exact tested

/--
Extract the original large-forest equation at a non-readout vertex of
`large \ small`.
-/
theorem HedgeWitness.smallOutcomePairBitsRealizes_outer
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (pairBits : Fin (pairRootCount G) → Bool)
    (realizes : w.smallOutcomePairBitsRealizes rich target pairBits = true)
    (child : Fin S.count) (inLarge : w.large child = true)
    (notSmall : w.small child = false)
    (notReadout : w.rootReadoutNodes child = false) :
    hedgeXorPairBitsWithinFrom G w.large child pairBits =
      hedgeForestRequiredIncidence rich w.child target child := by
  have member := (NodeSet.mem_members_iff w.large child).mpr inLarge
  have tested := (List.all_eq_true.mp realizes) child member
  simp [notSmall, notReadout] at tested
  exact tested

/--
The pair-root coordinates of every small-flow evaluation satisfy the custom
small support predicate, including its unconstrained outer-readout case.
-/
theorem HedgeWitness.smallOutcomeFlowModel_pairBitsRealizes_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    w.smallOutcomePairBitsRealizes rich
      ((w.smallOutcomeFlowModel rich).eval u) (hedgePairBitsOf G u) = true := by
  apply w.smallOutcomePairBitsRealizes_of rich
  · intro child inSmall
    have selected : w.smallOutcomeFlowNodes child = true := by
      simp [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union, inSmall]
    have equation := hedgeFlowReadoutModel_evalNodeUnder_bit rich
      w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
      w.smallOutcomeFlowSuccessor_wellFormed (w.smallParityModel rich)
      (hedgeForestIncidenceSource G w.small)
      (FiniteLatentSCM.noIntervention S) u child selected rfl
    simp only [hedgeForestIncidenceSource, inSmall, if_true] at equation
    have equation' :
        hedgeIsSecond rich child ((w.smallOutcomeFlowModel rich).eval u child) =
          Bool.xor
            (hedgeXorPairBitsWithin G w.small child
              (fun latent _ => u latent))
            (hedgeRoutingIncomingBits w.smallOutcomeFlowSuccessor
              (fun parent => hedgeIsSecond rich parent
                ((w.smallOutcomeFlowModel rich).eval u parent)) child) := by
      simpa only [FiniteLatentSCM.eval,
        HedgeWitness.smallOutcomeFlowModel] using equation
    rw [← hedgeForestParentBitsFrom_eq_routingIncomingBits rich
      w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
      w.smallOutcomeFlowSuccessor_wellFormed
      ((w.smallOutcomeFlowModel rich).eval u) child] at equation'
    rw [← hedgeXorPairBitsWithin_pairBitsOf G w.small u child]
    unfold hedgeForestRequiredIncidence
    rw [equation']
    generalize
      hedgeXorPairBitsWithin G w.small child (fun latent _ => u latent) = pair
    generalize hedgeForestParentBitsFrom rich w.smallOutcomeFlowSuccessor child
      (fun parent _ => (w.smallOutcomeFlowModel rich).eval u parent) = incoming
    cases pair <;> cases incoming <;> rfl
  · intro child inLarge notSmall notReadout
    have outsideFlow : w.smallOutcomeFlowNodes child = false := by
      simp [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
        notReadout, notSmall]
    have equation :
        hedgeIsSecond rich child
            ((w.smallOutcomeFlowModel rich).eval u child) =
          Bool.xor
            (hedgeXorPairBitsWithin G w.large child
              (fun latent _ => u latent))
            (hedgeForestParentBitsFrom rich w.child child
              (fun parent _ =>
                (w.smallOutcomeFlowModel rich).eval u parent)) := by
      change hedgeIsSecond rich child
          ((w.smallOutcomeFlowModel rich).evalNodeUnder
            (FiniteLatentSCM.noIntervention S) u child) = _
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      simp only [HedgeWitness.smallOutcomeFlowModel, hedgeFlowReadoutModel,
        outsideFlow, Bool.false_eq_true, ↓reduceIte,
        HedgeWitness.smallParityModel, hedgeNestedForestParityModel,
        notSmall]
      exact hedgeForestParityOutput_bit_of_mem G rich w.large w.child child
        _ _ inLarge
    rw [← hedgeXorPairBitsWithin_pairBitsOf G w.large u child]
    unfold hedgeForestRequiredIncidence
    rw [equation]
    generalize
      hedgeXorPairBitsWithin G w.large child (fun latent _ => u latent) = pair
    generalize hedgeForestParentBitsFrom rich w.child child
      (fun parent _ => (w.smallOutcomeFlowModel rich).eval u parent) = incoming
    cases pair <;> cases incoming <;> rfl

/-- A small-flow evaluation satisfies every source-free routing equation. -/
theorem HedgeWitness.smallOutcomeFlowModel_zeroSourceOutside_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeFlowZeroSourceOutside rich w.smallOutcomeFlowNodes w.small
      w.smallOutcomeFlowSuccessor ((w.smallOutcomeFlowModel rich).eval u) =
        true := by
  apply hedgeFlowZeroSourceOutside_of
  intro child selected outside
  have equation := hedgeFlowReadoutModel_evalNodeUnder_bit rich
    w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed (w.smallParityModel rich)
    (hedgeForestIncidenceSource G w.small)
    (FiniteLatentSCM.noIntervention S) u child selected rfl
  simp only [hedgeForestIncidenceSource, outside] at equation
  have equation' :
      hedgeIsSecond rich child ((w.smallOutcomeFlowModel rich).eval u child) =
        Bool.xor false
          (hedgeRoutingIncomingBits w.smallOutcomeFlowSuccessor (fun parent =>
            hedgeIsSecond rich parent
              ((w.smallOutcomeFlowModel rich).eval u parent)) child) := by
    simpa only [FiniteLatentSCM.eval,
      HedgeWitness.smallOutcomeFlowModel] using equation
  rw [← hedgeForestParentBitsFrom_eq_routingIncomingBits rich
    w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed
    ((w.smallOutcomeFlowModel rich).eval u) child] at equation'
  unfold hedgeForestRequiredIncidence
  rw [equation']
  generalize hedgeForestParentBitsFrom rich w.smallOutcomeFlowSuccessor child
    (fun parent _ => (w.smallOutcomeFlowModel rich).eval u parent) = incoming
  cases incoming <;> rfl

/-- Every small-flow evaluation lies in the common two-value target alphabet. -/
theorem HedgeWitness.smallOutcomeFlowModel_eval_valid
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgeParityTargetValid rich w.largeOutcomeFlowNodes
      ((w.smallOutcomeFlowModel rich).eval u) = true := by
  apply hedgeParityTargetValid_of
  intro child selected
  cases inFlow : w.smallOutcomeFlowNodes child with
  | true =>
      have flowValid := hedgeFlowReadoutModel_eval_valid rich
        w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
        (w.smallParityModel rich) (hedgeForestIncidenceSource G w.small) u
      exact hedgeParityTargetValid_spec rich w.smallOutcomeFlowNodes
        ((w.smallOutcomeFlowModel rich).eval u) flowValid child inFlow
  | false =>
      have notReadout : w.rootReadoutNodes child = false := by
        cases readout : w.rootReadoutNodes child with
        | false => rfl
        | true =>
            simp [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
              readout] at inFlow
      have notSmall : w.small child = false := by
        cases small : w.small child with
        | false => rfl
        | true =>
            simp [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
              small] at inFlow
      have inLarge : w.large child = true := by
        simpa [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
          notReadout] using selected
      change
        (w.smallOutcomeFlowModel rich).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u child = rich.first child ∨
          (w.smallOutcomeFlowModel rich).evalNodeUnder
              (FiniteLatentSCM.noIntervention S) u child = rich.second child
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      simp only [HedgeWitness.smallOutcomeFlowModel, hedgeFlowReadoutModel,
        inFlow, Bool.false_eq_true, ↓reduceIte,
        HedgeWitness.smallParityModel, hedgeNestedForestParityModel,
        notSmall]
      rw [hedgeForestParityOutput, if_pos inLarge]
      unfold hedgeParityValue
      split <;> simp

/--
Outside the common routed node set, small-flow evaluation preserves the same
private coordinate convention as the large model.
-/
theorem HedgeWitness.smallOutcomeFlowModel_privateCoordinatesFit_eval
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (u : (hedgeLatentExtension G).Assignment) :
    hedgePrivateCoordinatesFit w.largeOutcomeFlowNodes
      ((w.smallOutcomeFlowModel rich).eval u)
      (hedgePrivateCoordinatesOf G u) = true := by
  apply hedgePrivateCoordinatesFit_of
  intro child outside
  have outsideFlow : w.smallOutcomeFlowNodes child = false := by
    cases inFlow : w.smallOutcomeFlowNodes child with
    | false => rfl
    | true =>
        cases inReadout : w.rootReadoutNodes child with
        | true =>
            simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
              inReadout] at outside
        | false =>
            have inSmall : w.small child = true := by
              simpa [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
                inReadout] using inFlow
            have inLarge := w.small_subset_large child inSmall
            simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
              inLarge] at outside
  have outsideLarge : w.large child = false := by
    cases inLarge : w.large child with
    | false => rfl
    | true =>
        simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
          inLarge] at outside
  have outsideSmall : w.small child = false := by
    cases inSmall : w.small child with
    | false => rfl
    | true =>
        have inLarge := w.small_subset_large child inSmall
        rw [outsideLarge] at inLarge
        contradiction
  change hedgePrivateIndex G child (fun root _ => u root) =
    hedgeIndexOfValue S child ((w.smallOutcomeFlowModel rich).eval u child)
  have outputEq :
      (w.smallOutcomeFlowModel rich).eval u child =
        hedgePrivateDecode S child
          (hedgePrivateIndex G child (fun root _ => u root)) := by
    change
      (w.smallOutcomeFlowModel rich).evalNodeUnder
          (FiniteLatentSCM.noIntervention S) u child = _
    rw [FiniteLatentSCM.evalNodeUnder]
    unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
    simp [HedgeWitness.smallOutcomeFlowModel, hedgeFlowReadoutModel,
      outsideFlow, HedgeWitness.smallParityModel,
      hedgeNestedForestParityModel, outsideSmall,
      hedgeForestParityOutput, outsideLarge]
  have indexed := congrArg (hedgeIndexOfValue S child) outputEq
  rw [hedgeIndexOf_decode] at indexed
  exact indexed.symm

/--
Reconstruct one coordinate of a small-flow evaluation from its custom pair
constraints and the common private-coordinate constraints.
-/
theorem HedgeWitness.smallOutcomeFlowModel_evalNode_eq_of_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich w.largeOutcomeFlowNodes target = true)
    (zero : hedgeFlowZeroSourceOutside rich w.smallOutcomeFlowNodes w.small
      w.smallOutcomeFlowSuccessor target = true)
    (u : (hedgeLatentExtension G).Assignment)
    (realizes : w.smallOutcomePairBitsRealizes rich target
      (hedgePairBitsOf G u) = true)
    (privateFits : hedgePrivateCoordinatesFit w.largeOutcomeFlowNodes target
      (hedgePrivateCoordinatesOf G u) = true)
    (child : Fin S.count) :
    (w.smallOutcomeFlowModel rich).evalNodeUnder
        (FiniteLatentSCM.noIntervention S) u child = target child := by
  cases inFlow : w.smallOutcomeFlowNodes child with
  | true =>
      have sourceEq :
          (if w.small child then
              hedgeXorPairBitsWithin G w.small child
                (fun latent _ => u latent)
            else false) =
            hedgeForestRequiredIncidence rich w.smallOutcomeFlowSuccessor
              target child := by
        cases inSmall : w.small child with
        | true =>
            simp only [if_true]
            rw [hedgeXorPairBitsWithin_pairBitsOf]
            exact w.smallOutcomePairBitsRealizes_small rich target
              (hedgePairBitsOf G u) realizes child inSmall
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact (hedgeFlowZeroSourceOutside_spec rich
              w.smallOutcomeFlowNodes w.small w.smallOutcomeFlowSuccessor
              target zero child inFlow inSmall).symm
      have parents :
          hedgeForestParentBitsFrom rich w.smallOutcomeFlowSuccessor child
              (fun parent _ =>
                (w.smallOutcomeFlowModel rich).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent) =
            hedgeForestParentBitsFrom rich w.smallOutcomeFlowSuccessor child
              (fun parent _ => target parent) := by
        apply hedgeForestParentBitsFrom_congr rich child
        · intro _parent
          rfl
        · intro parent edge
          exact w.smallOutcomeFlowModel_evalNode_eq_of_support rich target
            valid zero u realizes privateFits parent
      rw [FiniteLatentSCM.evalNodeUnder]
      unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
      simp only [HedgeWitness.smallOutcomeFlowModel, hedgeFlowReadoutModel,
        inFlow, if_true, hedgeForestIncidenceSource]
      unfold HedgeWitness.smallOutcomeFlowModel at parents
      simp only [HedgeWitness.smallParityModel,
        hedgeNestedForestParityModel] at sourceEq parents ⊢
      unfold hedgeFlowReadoutModel FiniteLatentSCM.noIntervention at parents
      simp only [hedgeForestIncidenceSource] at parents
      rw [sourceEq, parents]
      unfold hedgeForestRequiredIncidence
      rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      have selected : w.largeOutcomeFlowNodes child = true := by
        cases inReadout : w.rootReadoutNodes child with
        | true =>
            simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
              inReadout]
        | false =>
            have inSmall : w.small child = true := by
              simpa [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
                inReadout] using inFlow
            have inLarge := w.small_subset_large child inSmall
            simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
              inLarge]
      exact hedgeParityValue_isSecond_of_valid rich child (target child)
        (hedgeParityTargetValid_spec rich w.largeOutcomeFlowNodes target
          valid child selected)
  | false =>
      have notReadout : w.rootReadoutNodes child = false := by
        cases readout : w.rootReadoutNodes child with
        | false => rfl
        | true =>
            simp [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
              readout] at inFlow
      have notSmall : w.small child = false := by
        cases small : w.small child with
        | false => rfl
        | true =>
            simp [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
              small] at inFlow
      cases inLarge : w.large child with
      | false =>
          have outsideLargeFlow : w.largeOutcomeFlowNodes child = false := by
            simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
              notReadout, inLarge]
          have privateAt := hedgePrivateCoordinatesFit_spec
            w.largeOutcomeFlowNodes target (hedgePrivateCoordinatesOf G u)
            privateFits child outsideLargeFlow
          change hedgePrivateIndex G child (fun root _ => u root) =
            hedgeIndexOfValue S child (target child) at privateAt
          rw [FiniteLatentSCM.evalNodeUnder]
          unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
          simp only [HedgeWitness.smallOutcomeFlowModel,
            hedgeFlowReadoutModel, inFlow, Bool.false_eq_true, ↓reduceIte,
            HedgeWitness.smallParityModel, hedgeNestedForestParityModel,
            notSmall]
          simp [hedgeForestParityOutput, inLarge, privateAt,
            hedgePrivateDecode_index]
      | true =>
          have sourceEq :
              hedgeXorPairBitsWithin G w.large child
                  (fun latent _ => u latent) =
                hedgeForestRequiredIncidence rich w.child target child := by
            rw [hedgeXorPairBitsWithin_pairBitsOf]
            exact w.smallOutcomePairBitsRealizes_outer rich target
              (hedgePairBitsOf G u) realizes child inLarge notSmall notReadout
          have parents :
              hedgeForestParentBitsFrom rich w.child child
                  (fun parent _ =>
                    (w.smallOutcomeFlowModel rich).evalNodeUnder
                      (FiniteLatentSCM.noIntervention S) u parent) =
                hedgeForestParentBitsFrom rich w.child child
                  (fun parent _ => target parent) := by
            apply hedgeForestParentBitsFrom_congr rich child
            · intro _parent
              rfl
            · intro parent edge
              exact w.smallOutcomeFlowModel_evalNode_eq_of_support rich target
                valid zero u realizes privateFits parent
          rw [FiniteLatentSCM.evalNodeUnder]
          unfold FiniteLatentSCM.equationUnder FiniteLatentSCM.noIntervention
          simp only [HedgeWitness.smallOutcomeFlowModel,
            hedgeFlowReadoutModel, inFlow, Bool.false_eq_true, ↓reduceIte,
            HedgeWitness.smallParityModel, hedgeNestedForestParityModel,
            notSmall]
          rw [hedgeForestParityOutput, if_pos inLarge]
          change hedgeParityValue rich child
            (Bool.xor
              (hedgeXorPairBitsWithin G w.large child (fun root _ => u root))
              (hedgeForestParentBitsFrom rich w.child child fun parent _ =>
                (w.smallOutcomeFlowModel rich).evalNodeUnder
                  (FiniteLatentSCM.noIntervention S) u parent)) = target child
          rw [sourceEq, parents]
          unfold hedgeForestRequiredIncidence
          rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
          have selected : w.largeOutcomeFlowNodes child = true := by
            simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union, inLarge]
          exact hedgeParityValue_isSecond_of_valid rich child (target child)
            (hedgeParityTargetValid_spec rich w.largeOutcomeFlowNodes target
              valid child selected)
termination_by child.val
decreasing_by
  all_goals exact S.directed_earlier edge

/-- Reconstruct the complete small-flow output from its support constraints. -/
theorem HedgeWitness.smallOutcomeFlowModel_eval_eq_of_support
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich w.largeOutcomeFlowNodes target = true)
    (zero : hedgeFlowZeroSourceOutside rich w.smallOutcomeFlowNodes w.small
      w.smallOutcomeFlowSuccessor target = true)
    (u : (hedgeLatentExtension G).Assignment)
    (realizes : w.smallOutcomePairBitsRealizes rich target
      (hedgePairBitsOf G u) = true)
    (privateFits : hedgePrivateCoordinatesFit w.largeOutcomeFlowNodes target
      (hedgePrivateCoordinatesOf G u) = true) :
    (w.smallOutcomeFlowModel rich).eval u = target := by
  funext child
  exact w.smallOutcomeFlowModel_evalNode_eq_of_support rich target valid zero
    u realizes privateFits child

/--
Exact support theorem for the small outcome-flow model, expressed using the
same coordinate-fiber enumerator as the large model.
-/
theorem HedgeWitness.smallOutcomeFlowModel_eval_mem_coordinateSupport_iff
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (valid : hedgeParityTargetValid rich w.largeOutcomeFlowNodes target = true)
    (zero : hedgeFlowZeroSourceOutside rich w.smallOutcomeFlowNodes w.small
      w.smallOutcomeFlowSuccessor target = true)
    (u : (hedgeLatentExtension G).Assignment) :
    (w.smallOutcomeFlowModel rich).eval u = target ↔
      u ∈ hedgeCoordinateSupportLatents G w.largeOutcomeFlowNodes target
        (w.smallOutcomePairBitsRealizes rich target) := by
  rw [hedgeCoordinateSupportLatents_mem_iff]
  constructor
  · intro evaluates
    subst target
    exact ⟨w.smallOutcomeFlowModel_pairBitsRealizes_eval rich u,
      w.smallOutcomeFlowModel_privateCoordinatesFit_eval rich u⟩
  · intro support
    exact w.smallOutcomeFlowModel_eval_eq_of_support rich target valid zero u
      support.1 support.2

/-! ## Comparing the two finite support fibers -/

/--
The incidence demanded from a small-model pair root: use the rerouted small
forest on `small`, and the original large forest elsewhere.
-/
def HedgeWitness.smallOutcomeRequiredIncidence
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) (child : Fin S.count) : Bool :=
  if w.small child then
    hedgeForestRequiredIncidence rich w.smallOutcomeFlowSuccessor target child
  else
    hedgeForestRequiredIncidence rich w.child target child

/--
If readout routing never re-enters `large \ small`, the custom small support
predicate is exactly the standard nested-forest incidence predicate.  This is
the precise geometric point at which the conditional theorem is used.
-/
theorem HedgeWitness.smallOutcomePairBitsRealizes_eq_nested_of_readout_inside
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (readoutInside : forall node, w.rootReadoutNodes node = true →
      w.large node = true → w.small node = true)
    (pairBits : Fin (pairRootCount G) → Bool) :
    w.smallOutcomePairBitsRealizes rich target pairBits =
      hedgeNestedPairBitsRealizes G w.large w.small
        (w.smallOutcomeRequiredIncidence rich target) pairBits := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro realizes
    apply hedgeNestedPairBitsRealizes_of
    intro child inLarge
    cases inSmall : w.small child with
    | true =>
        simp only [hedgeNestedXorPairBitsWithinFrom, inSmall, if_true,
          HedgeWitness.smallOutcomeRequiredIncidence]
        exact w.smallOutcomePairBitsRealizes_small rich target pairBits
          realizes child inSmall
    | false =>
        have notReadout : w.rootReadoutNodes child = false := by
          cases inReadout : w.rootReadoutNodes child with
          | false => rfl
          | true =>
              have inside := readoutInside child inReadout inLarge
              rw [inSmall] at inside
              contradiction
        simp only [hedgeNestedXorPairBitsWithinFrom, inSmall,
          Bool.false_eq_true, ↓reduceIte,
          HedgeWitness.smallOutcomeRequiredIncidence]
        exact w.smallOutcomePairBitsRealizes_outer rich target pairBits
          realizes child inLarge inSmall notReadout
  · intro realizes
    apply w.smallOutcomePairBitsRealizes_of rich
    · intro child inSmall
      have inLarge := w.small_subset_large child inSmall
      have atChild := hedgeNestedPairBitsRealizes_spec G w.large w.small
        (w.smallOutcomeRequiredIncidence rich target) pairBits realizes child
        inLarge
      simpa [hedgeNestedXorPairBitsWithinFrom,
        HedgeWitness.smallOutcomeRequiredIncidence, inSmall] using atChild
    · intro child inLarge notSmall notReadout
      have atChild := hedgeNestedPairBitsRealizes_spec G w.large w.small
        (w.smallOutcomeRequiredIncidence rich target) pairBits realizes child
        inLarge
      simpa [hedgeNestedXorPairBitsWithinFrom,
        HedgeWitness.smallOutcomeRequiredIncidence, notSmall] using atChild

/--
XOR conservation for an observable target: required incidences over all
routed nodes telescope to the observable parity at the retained sinks.
-/
theorem hedgeTargetFlow_conservation
    (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (target : S.Assignment) :
    hedgeNodeXor (keptSinks nodes successor)
        (fun node => hedgeIsSecond rich node (target node)) =
      hedgeNodeXor nodes
        (hedgeForestRequiredIncidence rich successor target) := by
  apply hedgeRoutingFlow_conservation nodes successor wellFormed
  intro node _selected
  unfold hedgeForestRequiredIncidence
  rw [hedgeForestParentBitsFrom_eq_routingIncomingBits rich nodes successor
    wellFormed target node]
  generalize hedgeIsSecond rich node (target node) = bit
  generalize hedgeRoutingIncomingBits successor
    (fun parent => hedgeIsSecond rich parent (target parent)) node = incoming
  cases bit <;> cases incoming <;> rfl

/--
Restrict target-flow conservation to the actual source set when every other
routed vertex has zero required incidence.
-/
theorem hedgeTargetFlow_conservation_of_zeroOutside
    (rich : ObservedSignature.ValueRich S)
    (nodes sourceNodes : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (sourceSubset : NodeSet.Subset sourceNodes nodes)
    (target : S.Assignment)
    (zero : hedgeFlowZeroSourceOutside rich nodes sourceNodes successor target =
      true) :
    hedgeNodeXor (keptSinks nodes successor)
        (fun node => hedgeIsSecond rich node (target node)) =
      hedgeNodeXor sourceNodes
        (hedgeForestRequiredIncidence rich successor target) := by
  rw [hedgeTargetFlow_conservation rich nodes successor wellFormed target,
    hedgeNodeXor_eq_inter_of_false_right nodes sourceNodes
      (hedgeForestRequiredIncidence rich successor target)]
  · have intersection : NodeSet.inter nodes sourceNodes = sourceNodes := by
      funext node
      cases source : sourceNodes node with
      | false => simp [NodeSet.inter, source]
      | true => simp [NodeSet.inter, source, sourceSubset node source]
    rw [intersection]
  · intro node selected outside
    exact hedgeFlowZeroSourceOutside_spec rich nodes sourceNodes successor
      target zero node selected outside

/--
The total incidence demanded from large pair roots is the parity read at the
common outcome sinks.
-/
theorem HedgeWitness.largeOutcomeRequiredIncidence_sinkParity
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (zero : hedgeFlowZeroSourceOutside rich w.largeOutcomeFlowNodes w.large
      w.largeOutcomeFlowSuccessor target = true) :
    hedgeNodeXor w.large
        (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor target) =
      hedgeNodeXor
        (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)
        (fun node => hedgeIsSecond rich node (target node)) := by
  symm
  rw [← w.largeOutcomeFlowSinks_eq_rootReadoutSinks]
  exact hedgeTargetFlow_conservation_of_zeroOutside rich
    w.largeOutcomeFlowNodes w.large w.largeOutcomeFlowSuccessor
    w.largeOutcomeFlowSuccessor_wellFormed
    (NodeSet.subset_union_right w.rootReadoutNodes w.large) target zero

/--
The total incidence demanded from small pair roots is the same parity at the
common outcome sinks.
-/
theorem HedgeWitness.smallOutcomeRequiredIncidence_sinkParity
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (zero : hedgeFlowZeroSourceOutside rich w.smallOutcomeFlowNodes w.small
      w.smallOutcomeFlowSuccessor target = true) :
    hedgeNodeXor w.small (w.smallOutcomeRequiredIncidence rich target) =
      hedgeNodeXor
        (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)
        (fun node => hedgeIsSecond rich node (target node)) := by
  have flow := hedgeTargetFlow_conservation_of_zeroOutside rich
    w.smallOutcomeFlowNodes w.small w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed
    (NodeSet.subset_union_right w.rootReadoutNodes w.small) target zero
  rw [w.smallOutcomeFlowSinks_eq_rootReadoutSinks] at flow
  rw [flow]
  unfold hedgeNodeXor
  apply foldl_congr_of_mem
  intro total child member
  have inSmall := (NodeSet.mem_members_iff w.small child).mp member
  simp [HedgeWitness.smallOutcomeRequiredIncidence, inSmall]

/--
The large and small incidence systems have the same solvability parity once
their source-free routing equations hold.
-/
theorem HedgeWitness.largeOutcomeRequiredEven_iff_smallOutcomeRequiredEven
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (largeZero : hedgeFlowZeroSourceOutside rich w.largeOutcomeFlowNodes
      w.large w.largeOutcomeFlowSuccessor target = true)
    (smallZero : hedgeFlowZeroSourceOutside rich w.smallOutcomeFlowNodes
      w.small w.smallOutcomeFlowSuccessor target = true) :
    (hedgeTrueVertices w.large
      (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor target)
        ).length % 2 = 0 ↔
      (hedgeTrueVertices w.small
        (w.smallOutcomeRequiredIncidence rich target)).length % 2 = 0 := by
  have parityEq :
      hedgeNodeXor w.large
          (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor
            target) =
        hedgeNodeXor w.small
          (w.smallOutcomeRequiredIncidence rich target) := by
    rw [w.largeOutcomeRequiredIncidence_sinkParity rich target largeZero,
      w.smallOutcomeRequiredIncidence_sinkParity rich target smallZero]
  constructor
  · intro largeEven
    have largeFalse :
        hedgeNodeXor w.large
          (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor
            target) = false :=
      (foldl_xor_eq_false_iff_filter_even
        (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor target)
        (NodeSet.members w.large)).mpr largeEven
    have smallFalse :
        hedgeNodeXor w.small
          (w.smallOutcomeRequiredIncidence rich target) = false := by
      rw [← parityEq]
      exact largeFalse
    exact (foldl_xor_eq_false_iff_filter_even
      (w.smallOutcomeRequiredIncidence rich target)
      (NodeSet.members w.small)).mp smallFalse
  · intro smallEven
    have smallFalse :
        hedgeNodeXor w.small
          (w.smallOutcomeRequiredIncidence rich target) = false :=
      (foldl_xor_eq_false_iff_filter_even
        (w.smallOutcomeRequiredIncidence rich target)
        (NodeSet.members w.small)).mpr smallEven
    have largeFalse :
        hedgeNodeXor w.large
          (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor
            target) = false := by
      rw [parityEq]
      exact smallFalse
    exact (foldl_xor_eq_false_iff_filter_even
      (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor target)
      (NodeSet.members w.large)).mp largeFalse

/--
Under no readout re-entry, the explicit lists of pair-root solutions for the
large and small systems have equal length.  The proof covers both the even
case, by the nested-forest counting theorem, and the odd case, where both
lists are empty.
-/
theorem HedgeWitness.outcomePairBitRealizers_length_eq_of_readout_inside
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (readoutInside : forall node, w.rootReadoutNodes node = true →
      w.large node = true → w.small node = true)
    (largeZero : hedgeFlowZeroSourceOutside rich w.largeOutcomeFlowNodes
      w.large w.largeOutcomeFlowSuccessor target = true)
    (smallZero : hedgeFlowZeroSourceOutside rich w.smallOutcomeFlowNodes
      w.small w.smallOutcomeFlowSuccessor target = true) :
    ((hedgePairBitEnum G).filter
      (hedgePairBitsRealizes G w.large
        (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor
          target))).length =
      ((hedgePairBitEnum G).filter
        (w.smallOutcomePairBitsRealizes rich target)).length := by
  have smallPredicateEq :
      w.smallOutcomePairBitsRealizes rich target =
        hedgeNestedPairBitsRealizes G w.large w.small
          (w.smallOutcomeRequiredIncidence rich target) := by
    funext pairBits
    exact w.smallOutcomePairBitsRealizes_eq_nested_of_readout_inside rich
      target readoutInside pairBits
  rw [smallPredicateEq]
  by_cases largeEven :
      (hedgeTrueVertices w.large
        (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor
          target)).length % 2 = 0
  · have smallEven :
        (hedgeTrueVertices w.small
          (w.smallOutcomeRequiredIncidence rich target)).length % 2 = 0 :=
      (w.largeOutcomeRequiredEven_iff_smallOutcomeRequiredEven rich target
        largeZero smallZero).mp largeEven
    exact w.large_forest.component.pairBitRealizers_length_eq_nested
      G w.large w.small w.small_forest.component w.small_subset_large
      (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor target)
      (w.smallOutcomeRequiredIncidence rich target) largeEven smallEven
  · have smallNotEven :
        (hedgeTrueVertices w.small
          (w.smallOutcomeRequiredIncidence rich target)).length % 2 ≠ 0 :=
      fun smallEven => largeEven
        ((w.largeOutcomeRequiredEven_iff_smallOutcomeRequiredEven rich target
          largeZero smallZero).mpr smallEven)
    rw [hedgePairBitRealizers_length_eq_zero_of_not_even G w.large
      (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor target)
      largeEven,
      hedgeNestedPairBitRealizers_length_eq_zero_of_not_even G w.large
        w.small w.small_subset_large
        (w.smallOutcomeRequiredIncidence rich target) smallNotEven]

/-! ## Aligning source-free equations outside the hedge -/

/--
The incoming-parent parity at `child` depends only on which parents the two
successor maps route into that child.
-/
theorem hedgeForestParentBitsFrom_congr_to_child
    (rich : ObservedSignature.ValueRich S) (child : Fin S.count)
    (leftKept rightKept : ForestChild S)
    (get : forall parent, S.directed parent child = true → S.Value parent)
    (sameIncoming : forall parent,
      leftKept parent = some child ↔ rightKept parent = some child) :
    hedgeForestParentBitsFrom rich leftKept child get =
      hedgeForestParentBitsFrom rich rightKept child get := by
  unfold hedgeForestParentBitsFrom
  apply foldl_congr
  intro total parent
  if edge : S.directed parent child = true then
    by_cases left : leftKept parent = some child
    · have right := (sameIncoming parent).mp left
      simp [edge, left, right]
    · have right : rightKept parent ≠ some child :=
        fun found => left ((sameIncoming parent).mpr found)
      simp [edge, left, right]
  else
    simp [edge]

/--
Outside `large`, the large and small composite successor maps select exactly
the same incoming routed parents.
-/
theorem HedgeWitness.outcomeFlowSuccessors_same_incoming_outside_large
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (child : Fin S.count)
    (outsideLarge : w.large child = false) :
    forall parent,
      w.largeOutcomeFlowSuccessor parent = some child ↔
        w.smallOutcomeFlowSuccessor parent = some child := by
  intro parent
  cases inReadout : w.rootReadoutNodes parent with
  | true =>
      simp [HedgeWitness.largeOutcomeFlowSuccessor,
        HedgeWitness.smallOutcomeFlowSuccessor, forestChildPrioritize,
        inReadout]
  | false =>
      cases inSmall : w.small parent with
      | true =>
          simp [HedgeWitness.largeOutcomeFlowSuccessor,
            HedgeWitness.smallOutcomeFlowSuccessor, forestChildPrioritize,
            inReadout, restrictChild, inSmall]
      | false =>
          constructor
          · intro found
            have childLarge := (w.large_forest.child_edge parent child (by
              simpa [HedgeWitness.largeOutcomeFlowSuccessor,
                forestChildPrioritize, inReadout] using found)).2.1
            rw [outsideLarge] at childLarge
            contradiction
          · intro found
            simp [HedgeWitness.smallOutcomeFlowSuccessor,
              forestChildPrioritize, inReadout, restrictChild, inSmall] at found

/--
Consequently, both outcome flows demand the same incidence at every vertex
outside `large`.
-/
theorem HedgeWitness.outcomeRequiredIncidence_eq_outside_large
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment) (child : Fin S.count)
    (outsideLarge : w.large child = false) :
    hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor target child =
      hedgeForestRequiredIncidence rich w.smallOutcomeFlowSuccessor target
        child := by
  unfold hedgeForestRequiredIncidence
  rw [hedgeForestParentBitsFrom_congr_to_child rich child
    w.largeOutcomeFlowSuccessor w.smallOutcomeFlowSuccessor
    (fun parent _ => target parent)
    (w.outcomeFlowSuccessors_same_incoming_outside_large child outsideLarge)]

/--
Under no readout re-entry, a target satisfies the source-free equations of
the large flow exactly when it satisfies those of the small flow.
-/
theorem HedgeWitness.outcomeFlowZeroSource_iff_of_readout_inside
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (readoutInside : forall node, w.rootReadoutNodes node = true →
      w.large node = true → w.small node = true) :
    hedgeFlowZeroSourceOutside rich w.largeOutcomeFlowNodes w.large
        w.largeOutcomeFlowSuccessor target = true ↔
      hedgeFlowZeroSourceOutside rich w.smallOutcomeFlowNodes w.small
        w.smallOutcomeFlowSuccessor target = true := by
  constructor
  · intro largeZero
    apply hedgeFlowZeroSourceOutside_of
    intro child inSmallFlow outsideSmall
    have inReadout : w.rootReadoutNodes child = true := by
      cases readout : w.rootReadoutNodes child with
      | true => rfl
      | false =>
          have inSmall : w.small child = true := by
            simpa [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
              readout] using inSmallFlow
          rw [outsideSmall] at inSmall
          contradiction
    have outsideLarge : w.large child = false := by
      cases inLarge : w.large child with
      | false => rfl
      | true =>
          have inSmall := readoutInside child inReadout inLarge
          rw [outsideSmall] at inSmall
          contradiction
    have inLargeFlow : w.largeOutcomeFlowNodes child = true := by
      simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union, inReadout]
    rw [← w.outcomeRequiredIncidence_eq_outside_large rich target child
      outsideLarge]
    exact hedgeFlowZeroSourceOutside_spec rich w.largeOutcomeFlowNodes w.large
      w.largeOutcomeFlowSuccessor target largeZero child inLargeFlow
      outsideLarge
  · intro smallZero
    apply hedgeFlowZeroSourceOutside_of
    intro child inLargeFlow outsideLarge
    have inReadout : w.rootReadoutNodes child = true := by
      cases readout : w.rootReadoutNodes child with
      | true => rfl
      | false =>
          simp [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union,
            readout, outsideLarge] at inLargeFlow
    have outsideSmall : w.small child = false := by
      cases inSmall : w.small child with
      | false => rfl
      | true =>
          have inLarge := w.small_subset_large child inSmall
          rw [outsideLarge] at inLarge
          contradiction
    have inSmallFlow : w.smallOutcomeFlowNodes child = true := by
      simp [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union, inReadout]
    rw [w.outcomeRequiredIncidence_eq_outside_large rich target child
      outsideLarge]
    exact hedgeFlowZeroSourceOutside_spec rich w.smallOutcomeFlowNodes w.small
      w.smallOutcomeFlowSuccessor target smallZero child inSmallFlow
      outsideSmall

/--
Lift pair-root equicardinality to the full latent coordinate fibers by using
their shared private-coordinate factor.
-/
theorem HedgeWitness.outcomeCoordinateSupport_length_eq_of_readout_inside
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (target : S.Assignment)
    (readoutInside : forall node, w.rootReadoutNodes node = true →
      w.large node = true → w.small node = true)
    (largeZero : hedgeFlowZeroSourceOutside rich w.largeOutcomeFlowNodes
      w.large w.largeOutcomeFlowSuccessor target = true)
    (smallZero : hedgeFlowZeroSourceOutside rich w.smallOutcomeFlowNodes
      w.small w.smallOutcomeFlowSuccessor target = true) :
    (hedgeCoordinateSupportLatents G w.largeOutcomeFlowNodes target
      (hedgePairBitsRealizes G w.large
        (hedgeForestRequiredIncidence rich w.largeOutcomeFlowSuccessor
          target))).length =
      (hedgeCoordinateSupportLatents G w.largeOutcomeFlowNodes target
        (w.smallOutcomePairBitsRealizes rich target)).length := by
  rw [hedgeCoordinateSupportLatents_length,
    hedgeCoordinateSupportLatents_length,
    w.outcomePairBitRealizers_length_eq_of_readout_inside rich target
      readoutInside largeZero smallZero]

/-! ## Observational equality and the conditional counterexample -/

/-- A singleton event that no latent assignment reaches has probability zero. -/
theorem FiniteLatentSCM.observationalSingleton_equiv_zero_of_never
    (model : FiniteLatentSCM S) (target : S.Assignment)
    (never : forall u : model.latent.Assignment,
      FiniteProbRecord.singletonEvent target (model.eval u) = false) :
    QProb.Equiv
      (model.observationalValue (FiniteProbRecord.singletonEvent target))
      QProb.zero :=
  QProb.equiv_trans
    (model.observationalValue_eq (FiniteProbRecord.singletonEvent target))
    (QProb.equiv_trans
      (model.prior.probVal_congr _ _ never)
      model.prior.probVal_false)

/--
Under no readout re-entry, the large and small outcome-flow models assign
equivalent probability to every observable singleton.  Invalid targets and
targets violating a source-free equation have zero mass on both sides; every
remaining target has equally many uniform latent preimages.
-/
theorem HedgeWitness.outcomeFlowModels_observational_singleton_equiv_of_readout_inside
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (readoutInside : forall node, w.rootReadoutNodes node = true →
      w.large node = true → w.small node = true)
    (target : S.Assignment) :
    QProb.Equiv
      ((w.largeOutcomeFlowModel rich).observationalValue
        (FiniteProbRecord.singletonEvent target))
      ((w.smallOutcomeFlowModel rich).observationalValue
        (FiniteProbRecord.singletonEvent target)) := by
  cases valid : hedgeParityTargetValid rich w.largeOutcomeFlowNodes target with
  | false =>
      have largeNever (u : (hedgeLatentExtension G).Assignment) :
          FiniteProbRecord.singletonEvent target
              ((w.largeOutcomeFlowModel rich).eval u) = false := by
        apply Bool.eq_false_iff.mpr
        intro holds
        have evaluates : (w.largeOutcomeFlowModel rich).eval u = target :=
          of_decide_eq_true (by
            simpa [FiniteProbRecord.singletonEvent] using holds)
        have outputValid := hedgeFlowReadoutModel_eval_valid rich
          w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
          (w.largeParityModel rich) (hedgeForestIncidenceSource G w.large) u
        change hedgeParityTargetValid rich w.largeOutcomeFlowNodes
          ((w.largeOutcomeFlowModel rich).eval u) = true at outputValid
        rw [evaluates, valid] at outputValid
        contradiction
      have smallNever (u : (hedgeLatentExtension G).Assignment) :
          FiniteProbRecord.singletonEvent target
              ((w.smallOutcomeFlowModel rich).eval u) = false := by
        apply Bool.eq_false_iff.mpr
        intro holds
        have evaluates : (w.smallOutcomeFlowModel rich).eval u = target :=
          of_decide_eq_true (by
            simpa [FiniteProbRecord.singletonEvent] using holds)
        have outputValid := w.smallOutcomeFlowModel_eval_valid rich u
        rw [evaluates, valid] at outputValid
        contradiction
      exact QProb.equiv_trans
        ((w.largeOutcomeFlowModel rich
          ).observationalSingleton_equiv_zero_of_never target largeNever)
        (QProb.equiv_symm
          ((w.smallOutcomeFlowModel rich
            ).observationalSingleton_equiv_zero_of_never target smallNever))
  | true =>
      cases largeZero : hedgeFlowZeroSourceOutside rich
        w.largeOutcomeFlowNodes w.large w.largeOutcomeFlowSuccessor target with
      | false =>
          have smallZeroFalse :
              hedgeFlowZeroSourceOutside rich w.smallOutcomeFlowNodes w.small
                w.smallOutcomeFlowSuccessor target = false := by
            cases smallZero : hedgeFlowZeroSourceOutside rich
              w.smallOutcomeFlowNodes w.small w.smallOutcomeFlowSuccessor target
            with
            | false => rfl
            | true =>
                have largeTrue :=
                  (w.outcomeFlowZeroSource_iff_of_readout_inside rich target
                    readoutInside).mpr smallZero
                rw [largeZero] at largeTrue
                contradiction
          have largeNever (u : (hedgeLatentExtension G).Assignment) :
              FiniteProbRecord.singletonEvent target
                  ((w.largeOutcomeFlowModel rich).eval u) = false := by
            apply Bool.eq_false_iff.mpr
            intro holds
            have evaluates : (w.largeOutcomeFlowModel rich).eval u = target :=
              of_decide_eq_true (by
                simpa [FiniteProbRecord.singletonEvent] using holds)
            have outputZero :=
              w.largeOutcomeFlowModel_zeroSourceOutside_eval rich u
            rw [evaluates, largeZero] at outputZero
            contradiction
          have smallNever (u : (hedgeLatentExtension G).Assignment) :
              FiniteProbRecord.singletonEvent target
                  ((w.smallOutcomeFlowModel rich).eval u) = false := by
            apply Bool.eq_false_iff.mpr
            intro holds
            have evaluates : (w.smallOutcomeFlowModel rich).eval u = target :=
              of_decide_eq_true (by
                simpa [FiniteProbRecord.singletonEvent] using holds)
            have outputZero :=
              w.smallOutcomeFlowModel_zeroSourceOutside_eval rich u
            rw [evaluates, smallZeroFalse] at outputZero
            contradiction
          exact QProb.equiv_trans
            ((w.largeOutcomeFlowModel rich
              ).observationalSingleton_equiv_zero_of_never target largeNever)
            (QProb.equiv_symm
              ((w.smallOutcomeFlowModel rich
                ).observationalSingleton_equiv_zero_of_never target smallNever))
      | true =>
          have smallZero :=
            (w.outcomeFlowZeroSource_iff_of_readout_inside rich target
              readoutInside).mp largeZero
          let largeSupport :=
            hedgeCoordinateSupportLatents G w.largeOutcomeFlowNodes target
              (hedgePairBitsRealizes G w.large
                (hedgeForestRequiredIncidence rich
                  w.largeOutcomeFlowSuccessor target))
          let smallSupport :=
            hedgeCoordinateSupportLatents G w.largeOutcomeFlowNodes target
              (w.smallOutcomePairBitsRealizes rich target)
          have largeEvalIff (u : (hedgeLatentExtension G).Assignment) :
              (w.largeOutcomeFlowModel rich).eval u = target ↔
                u ∈ largeSupport := by
            simpa [largeSupport] using
              w.largeOutcomeFlowModel_eval_mem_coordinateSupport_iff rich
                target valid largeZero u
          have smallEvalIff (u : (hedgeLatentExtension G).Assignment) :
              (w.smallOutcomeFlowModel rich).eval u = target ↔
                u ∈ smallSupport := by
            simpa [smallSupport] using
              w.smallOutcomeFlowModel_eval_mem_coordinateSupport_iff rich
                target valid smallZero u
          have largeEvent (u : (hedgeLatentExtension G).Assignment) :
              FiniteProbRecord.singletonEvent target
                  ((w.largeOutcomeFlowModel rich).eval u) =
                FiniteProbRecord.membershipEvent largeSupport u := by
            apply Bool.eq_iff_iff.mpr
            simpa only [FiniteProbRecord.singletonEvent,
              FiniteProbRecord.membershipEvent, decide_eq_true_eq] using
                largeEvalIff u
          have smallEvent (u : (hedgeLatentExtension G).Assignment) :
              FiniteProbRecord.singletonEvent target
                  ((w.smallOutcomeFlowModel rich).eval u) =
                FiniteProbRecord.membershipEvent smallSupport u := by
            apply Bool.eq_iff_iff.mpr
            simpa only [FiniteProbRecord.singletonEvent,
              FiniteProbRecord.membershipEvent, decide_eq_true_eq] using
                smallEvalIff u
          have largeMembership :
              QProb.Equiv
                ((w.largeOutcomeFlowModel rich).prior.probVal fun u =>
                  FiniteProbRecord.singletonEvent target
                    ((w.largeOutcomeFlowModel rich).eval u))
                ((w.largeOutcomeFlowModel rich).prior.probVal
                  (FiniteProbRecord.membershipEvent largeSupport)) :=
            (w.largeOutcomeFlowModel rich).prior.probVal_congr _ _ largeEvent
          have smallMembership :
              QProb.Equiv
                ((w.smallOutcomeFlowModel rich).prior.probVal fun u =>
                  FiniteProbRecord.singletonEvent target
                    ((w.smallOutcomeFlowModel rich).eval u))
                ((w.smallOutcomeFlowModel rich).prior.probVal
                  (FiniteProbRecord.membershipEvent smallSupport)) :=
            (w.smallOutcomeFlowModel rich).prior.probVal_congr _ _ smallEvent
          have largeSum := FiniteProbRecord.probVal_membership_equiv_listSum
            (w.largeOutcomeFlowModel rich).prior largeSupport
            (by
              simpa [largeSupport] using
                hedgeCoordinateSupportLatents_nodup G
                  w.largeOutcomeFlowNodes target
                  (hedgePairBitsRealizes G w.large
                    (hedgeForestRequiredIncidence rich
                      w.largeOutcomeFlowSuccessor target)))
          have smallSum := FiniteProbRecord.probVal_membership_equiv_listSum
            (w.smallOutcomeFlowModel rich).prior smallSupport
            (by
              simpa [smallSupport] using
                hedgeCoordinateSupportLatents_nodup G
                  w.largeOutcomeFlowNodes target
                  (w.smallOutcomePairBitsRealizes rich target))
          have supportLength : largeSupport.length = smallSupport.length := by
            simpa [largeSupport, smallSupport] using
              w.outcomeCoordinateSupport_length_eq_of_readout_inside rich
                target readoutInside largeZero smallZero
          have atomEquiv
              (left right : (hedgeLatentExtension G).Assignment) :
              QProb.Equiv
                ((w.largeOutcomeFlowModel rich).prior.probVal
                  (FiniteProbRecord.singletonEvent left))
                ((w.smallOutcomeFlowModel rich).prior.probVal
                  (FiniteProbRecord.singletonEvent right)) := by
            change QProb.Equiv
              ((FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
                (hedgeLatentFactor G)).probVal
                  (FiniteProbRecord.singletonEvent left))
              ((FiniteProduct.record (hedgeLatentCount G) (hedgeLatentValue G)
                (hedgeLatentFactor G)).probVal
                  (FiniteProbRecord.singletonEvent right))
            exact hedgePrior_singleton_equiv G left right
          have equalSums :=
            FiniteProbRecord.listSum_singletons_equiv_of_length
              (w.largeOutcomeFlowModel rich).prior
              (w.smallOutcomeFlowModel rich).prior
              largeSupport smallSupport supportLength atomEquiv
          exact QProb.equiv_trans
            ((w.largeOutcomeFlowModel rich).observationalValue_eq
              (FiniteProbRecord.singletonEvent target))
            (QProb.equiv_trans largeMembership
              (QProb.equiv_trans largeSum
                (QProb.equiv_trans equalSums
                  (QProb.equiv_trans (QProb.equiv_symm smallSum)
                    (QProb.equiv_trans (QProb.equiv_symm smallMembership)
                      (QProb.equiv_symm
                        ((w.smallOutcomeFlowModel rich).observationalValue_eq
                          (FiniteProbRecord.singletonEvent target))))))))

/--
Extend singleton equality over the finite assignment enumeration to full
observational equivalence of the two outcome-flow models.
-/
theorem HedgeWitness.outcomeFlowModels_observationally_equivalent_of_readout_inside
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (readoutInside : forall node, w.rootReadoutNodes node = true →
      w.large node = true → w.small node = true) :
    ObservationallyEquivalent (w.largeOutcomeFlowModel rich)
      (w.smallOutcomeFlowModel rich) := by
  intro event
  exact FiniteProbRecord.probVal_extensional_of_singletons
    (w.largeOutcomeFlowModel rich).observationalDist
    (w.smallOutcomeFlowModel rich).observationalDist
    S.assignmentEnumeration S.assignmentEnumeration_nodup
    S.assignmentEnumeration_complete
    (w.outcomeFlowModels_observational_singleton_equiv_of_readout_inside rich
      readoutInside) event

/--
Package the two compatible, observationally equivalent, query-separated flow
models as an unrestricted counterexample for the original query.  This
constructor deliberately claims neither strict positivity nor the general
case where a readout route re-enters `large \ small`.
-/
def HedgeWitness.outcomeFlowCounterexample_of_readout_inside
    {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (readoutInside : forall node, w.rootReadoutNodes node = true →
      w.large node = true → w.small node = true) :
    CounterexampleIn (GraphModelClass.all G) q where
  left := w.largeOutcomeFlowModel rich
  right := w.smallOutcomeFlowModel rich
  left_mem := w.largeOutcomeFlowModel_compatible rich
  right_mem := w.smallOutcomeFlowModel_compatible rich
  observationally_equal :=
    w.outcomeFlowModels_observationally_equivalent_of_readout_inside rich
      readoutInside
  query_separated := w.outcomeFlowModels_query_separated rich

end Causality
end Thesis
