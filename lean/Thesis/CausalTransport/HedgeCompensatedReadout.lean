import Thesis.CausalTransport.HedgeCarrierReplayPlan
import Thesis.CausalTransport.HedgeReadoutEvaluation
import Thesis.CausalTransport.HedgeOutcomeFlow

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Mechanism-compensated positive carrier outcome flows

An internal readout cannot just copy the routing parents and inject the old
bit at common roots.  The old bit supplied to the readout is the mechanism's
response at its *current* parents.  It already contains kept-parent parity;
adding a routed parent a second time can cancel the desired signal.

The plan here compensates that response.  At every small-forest row it
injects the old mechanism bit, removes its original kept-parent contribution,
and adds the composed forest/outcome-flow contribution.  At an outside-forest
route row it injects only the new flow parents.  All small rows are installed,
including rows off the explicit route: rerouting a kept parent can remove
an input at its old child, and that child's equation must be adjusted too.

The two models use the very same readouts.  For the nested carrier, excluded
outer-only parents cancel between the old and new full maps, leaving exactly
the small composed flow.  No outer-only vertex is rerouted.  Retained-state
replay proves equality of the full observational laws; restoring bits retain
strict positivity on every observed alphabet; private noise retains graph
compatibility.  The final theorems identify the actual folded mechanisms and
their local interventional equations with the compensated flows.

These are actual local flow equations, together with a global nested-sink
identity carrying the original weighted defect and all fresh private bits.
The general large-model root-parity comparison, integration of the fresh
biased factors, and the remaining conditional denominator cases must still
be proved before these plans yield general positive countermodels.  Routes
entering the outer-only forest remain outside this construction.
-/

/-- The exogenous residual of an original carrier row, recovered from its
factual bit and factual kept parents.  It includes any original private
defect, but not the newly installed readout noise. -/
def hedgeCarrierResidualBit (rich : ObservedSignature.ValueRich S) (kept : ForestChild S)
    (sample : S.Assignment) (child : Fin S.count) : Bool :=
  Bool.xor (hedgeIsSecond rich child (sample child))
    (hedgeForestParentBitsFrom rich kept child (fun parent _edge => sample parent))

/-- The original large carrier's free row has the same residual under
arbitrary interventions.  Only its current kept-parent parity changes.
This is the original-equation side of a compensated flow comparison. -/
theorem HedgeWitness.largeCarrierDefectParityModel_evalUnder_residual_bit
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (child : Fin S.count) (inside : w.large child = true) (free : intervention child = none) :
    hedgeIsSecond rich child ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit child) =
      Bool.xor (hedgeCarrierResidualBit rich w.child ((w.largeCarrierDefectParityModel rich).eval unit) child)
        (hedgeForestParentBitsFrom rich w.child child
          (fun parent _edge => (w.largeCarrierDefectParityModel rich).evalUnder intervention unit parent)) := by
  change hedgeIsSecond rich child (FiniteLatentSCM.evalNodeUnder _ intervention unit child) = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [free, w.largeCarrierDefectParityModel_mechanism_parent_response rich unit child]
  simp only [if_pos inside, hedgeIsSecond_parityCarrierValue, hedgeCarrierResidualBit]
  rfl

/-- One compensated instruction.  Inside the forest it replaces the old
incoming parity, rather than adding another copy of it.  Outside the forest
there is no incidence source to inject.  Both signals use declared parents
only; the fresh Boolean remains private to this child. -/
def HedgeWitness.carrierFlowReadoutStep {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (child : Fin S.count) : HedgeReadoutStep S where
  pivot := child
  noise := noise child
  injectOld := w.large child
  parentSignal := fun parents =>
    if w.large child then Bool.xor
      (hedgeForestParentBitsFrom rich w.child child parents)
      (hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child parents)
    else hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child parents

/-- Install all small-forest rows together with the outside route rows.
This is larger than a root-only route sweep, because old children of rerouted
vertices must lose their obsolete inputs.  The finite member list supplies
distinct pivots and an explicit private factor at each row. -/
def HedgeWitness.carrierFlowReadoutPlan {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) : List (HedgeReadoutStep S) :=
  (NodeSet.members w.smallOutcomeFlowNodes).map (w.carrierFlowReadoutStep rich noise)

namespace HedgeCompensatedReadout

variable {G : ObservedGraph S} {q : JointKernelQuery S}

private theorem pivots_distinct (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) :
    (w.carrierFlowReadoutPlan rich noise).Pairwise (fun first second => first.pivot ≠ second.pivot) :=
  List.Pairwise.map (w.carrierFlowReadoutStep rich noise) (fun _ _ different => different)
    (NodeSet.nodup_members w.smallOutcomeFlowNodes)

private theorem listed (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true) :
    w.carrierFlowReadoutStep rich noise child ∈ w.carrierFlowReadoutPlan rich noise :=
  List.mem_map.mpr ⟨child, (NodeSet.mem_members_iff w.smallOutcomeFlowNodes child).mpr selected, rfl⟩

private theorem plan_allowed (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false) :
    forall step, step ∈ w.carrierFlowReadoutPlan rich noise ->
      w.small step.pivot = true ∨ w.large step.pivot = false := by
  intro step member
  rcases List.mem_map.mp member with ⟨node, selected, same⟩
  subst step
  have inFlow := (NodeSet.mem_members_iff w.smallOutcomeFlowNodes node).mp selected
  have unionSelected : w.rootReadoutNodes node = true ∨ w.small node = true := Bool.or_eq_true_iff.mp inFlow
  cases unionSelected with
  | inl routed => exact allowed node routed
  | inr inside => exact Or.inl inside

private theorem small_of_flow_of_large (w : HedgeWitness G q)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true) (inside : w.large child = true) :
    w.small child = true := by
  have unionSelected : w.rootReadoutNodes child = true ∨ w.small child = true := Bool.or_eq_true_iff.mp selected
  cases unionSelected with
  | inr small => exact small
  | inl routed =>
      cases allowed child routed with
      | inl small => exact small
      | inr outside => rw [outside] at inside; cases inside

/-- An outside route vertex has no old kept edge, while a small route
vertex is retained by restriction.  This supplies the precise map-level
cancellation condition; no parent values are assumed unchanged. -/
private theorem outside_ready (w : HedgeWitness G q)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false) :
    forall parent, w.small parent = false -> w.rootReadoutNodes parent = true -> w.child parent = none := by
  intro parent outside routed
  cases allowed parent routed with
  | inl inside => rw [inside] at outside; cases outside
  | inr absent => exact w.large_forest.child_off_set parent absent

private theorem plan_noise_positive (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (positive : forall node, w.smallOutcomeFlowNodes node = true ->
      forall bit, (noise node).EventPositive (FiniteProbRecord.singletonEvent bit)) :
    forall step, step ∈ w.carrierFlowReadoutPlan rich noise ->
      forall bit, step.noise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  intro step member bit
  rcases List.mem_map.mp member with ⟨node, selected, same⟩
  subst step
  exact positive node ((NodeSet.mem_members_iff w.smallOutcomeFlowNodes node).mp selected) bit

/-! ## Compensated local responses at arbitrary current parents -/

private theorem large_response_bit (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (child : Fin S.count) (parents : S.ParentValues child) (bit : Bool) :
    hedgeIsSecond rich child
        (hedgeNoisyReadout rich child (w.carrierFlowReadoutStep rich noise child).injectOld
          (w.carrierFlowReadoutStep rich noise child).parentSignal parents
          ((w.largeCarrierDefectParityModel rich).mechanism child parents (fun root _incident => unit root)) bit) =
      Bool.xor
        (Bool.xor (if w.large child then hedgeCarrierResidualBit rich w.child
          ((w.largeCarrierDefectParityModel rich).eval unit) child else false)
          (hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child parents)) bit := by
  simp only [hedgeNoisyReadout, hedgeIsSecond_parityCarrierValue, HedgeWitness.carrierFlowReadoutStep]
  by_cases inside : w.large child = true
  ·
      simp only [if_pos inside]
      rw [w.largeCarrierDefectParityModel_mechanism_parent_response rich unit child parents]
      simp only [inside, if_true, hedgeIsSecond_parityCarrierValue, hedgeCarrierResidualBit]
      have cancels (source old new : Bool) : Bool.xor (Bool.xor source old) (Bool.xor old new) =
          Bool.xor source new := by cases source <;> cases old <;> cases new <;> rfl
      rw [cancels]
  · simp only [if_neg inside, Bool.false_xor]

private theorem small_response_bit (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (unit : (w.smallCarrierDefectParityModel rich).latent.Assignment)
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true)
    (parents : S.ParentValues child) (bit : Bool) :
    hedgeIsSecond rich child
        (hedgeNoisyReadout rich child (w.carrierFlowReadoutStep rich noise child).injectOld
          (w.carrierFlowReadoutStep rich noise child).parentSignal parents
          ((w.smallCarrierDefectParityModel rich).mechanism child parents (fun root _incident => unit root)) bit) =
      Bool.xor
        (Bool.xor (if w.small child then hedgeCarrierResidualBit rich (restrictChild w.small w.child)
          ((w.smallCarrierDefectParityModel rich).eval unit) child else false)
          (hedgeForestParentBitsFrom rich w.smallOutcomeFlowSuccessor child parents)) bit := by
  simp only [hedgeNoisyReadout, hedgeIsSecond_parityCarrierValue, HedgeWitness.carrierFlowReadoutStep]
  by_cases inside : w.large child = true
  ·
      have inSmall := small_of_flow_of_large w allowed child selected inside
      simp only [if_pos inside, if_pos inSmall]
      rw [w.smallCarrierDefectParityModel_mechanism_parent_response rich unit child parents]
      simp only [inside, inSmall, if_true, hedgeIsSecond_parityCarrierValue, hedgeCarrierResidualBit]
      have compensated : Bool.xor (hedgeForestParentBitsFrom rich (restrictChild w.small w.child) child parents)
          (Bool.xor (hedgeForestParentBitsFrom rich w.child child parents)
            (hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child parents)) =
          hedgeForestParentBitsFrom rich w.smallOutcomeFlowSuccessor child parents :=
        hedgeForestParentBitsFrom_compensate_prioritize_restrict rich w.small w.rootReadoutNodes
          w.child w.rootReadoutSuccessor child parents (outside_ready w allowed)
      congr 1
      rw [Bool.xor_assoc, compensated]
  ·
      have outsideLarge : w.large child = false := Bool.eq_false_iff.mpr inside
      have outsideSmall : w.small child = false := by
        cases selectedSmall : w.small child with
        | false => rfl
        | true => exact False.elim (inside (w.small_subset_large child selectedSmall))
      simp only [if_neg inside, Bool.false_eq_true, if_false, outsideSmall, Bool.false_xor]
      rw [hedgeForestParentBitsFrom_congr_to_child rich child w.largeOutcomeFlowSuccessor
        w.smallOutcomeFlowSuccessor parents (w.outcomeFlowSuccessors_same_incoming_outside_large child outsideLarge)]

end HedgeCompensatedReadout

/-! ## The actual folded model pair remains positive and observationally equal -/

/-- Compensating kept inputs preserves the entire observational law of the
carrier pair.  Internal pivots and removed inputs at their old children are
covered by the finite retained-state replay, not assumed non-influential. -/
theorem HedgeWitness.carrierDefectParityModels_carrierFlowReadoutPlan_observationally_equivalent
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false) :
    ObservationallyEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise))
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)) :=
  w.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_of_small_or_outside rich _
    (HedgeCompensatedReadout.plan_allowed w rich noise allowed)

/-- Restoring each installed row recovers every old full target assignment,
including nonbinary backgrounds.  Positive support of both fresh values is
enough; no bias or non-influence premise is used for positivity. -/
theorem HedgeWitness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_positive
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (positive : forall node, w.smallOutcomeFlowNodes node = true ->
      forall bit, (noise node).EventPositive (FiniteProbRecord.singletonEvent bit)) :
    ObservationallyPositive
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)) :=
  FiniteLatentSCM.withHedgeReadouts_positive _ (w.largeCarrierDefectParityModel_positive rich) rich _
    (HedgeCompensatedReadout.plan_noise_positive w rich noise positive)

/-- The identical restoring construction preserves full support of the
nested carrier, in the same plan used by observational and flow equations. -/
theorem HedgeWitness.smallCarrierDefectParityModel_carrierFlowReadoutPlan_positive
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (positive : forall node, w.smallOutcomeFlowNodes node = true ->
      forall bit, (noise node).EventPositive (FiniteProbRecord.singletonEvent bit)) :
    ObservationallyPositive
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)) :=
  FiniteLatentSCM.withHedgeReadouts_positive _ (w.smallCarrierDefectParityModel_positive rich) rich _
    (HedgeCompensatedReadout.plan_noise_positive w rich noise positive)

/-! ## Actual mechanism and interventional flow equations -/

/-- Every installed large-carrier row has precisely the new composed flow
parents and its original exogenous residual, followed by the fresh bit. -/
theorem HedgeWitness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_mechanism_bit
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true) (parents : S.ParentValues child) :
    hedgeIsSecond rich child
      (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).mechanism
        child parents (fun root _incident => (w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
          (w.carrierFlowReadoutPlan rich noise) unit root)) =
      Bool.xor (Bool.xor (if w.large child then hedgeCarrierResidualBit rich w.child
        ((w.largeCarrierDefectParityModel rich).eval unit) child else false)
        (hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child parents)) (bits child) := by
  have mechanism := FiniteLatentSCM.withHedgeReadouts_mechanism_of_mem (w.largeCarrierDefectParityModel rich) rich
    (w.carrierFlowReadoutPlan rich noise) (HedgeCompensatedReadout.pivots_distinct w rich noise)
    (w.carrierFlowReadoutStep rich noise child) (HedgeCompensatedReadout.listed w rich noise child selected)
    bits unit parents
  exact (congrArg (hedgeIsSecond rich child) mechanism).trans
    (HedgeCompensatedReadout.large_response_bit w rich noise unit child parents (bits child))

/-- The same installed readouts yield the nested composed flow, not the
large map incorrectly reused at small rows.  The excluded contributions
cancel at arbitrary current parent values, including intervention values. -/
theorem HedgeWitness.smallCarrierDefectParityModel_carrierFlowReadoutPlan_mechanism_bit
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (bits : Fin S.count -> Bool) (unit : (w.smallCarrierDefectParityModel rich).latent.Assignment)
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true) (parents : S.ParentValues child) :
    hedgeIsSecond rich child
      (((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).mechanism
        child parents (fun root _incident => (w.smallCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
          (w.carrierFlowReadoutPlan rich noise) unit root)) =
      Bool.xor (Bool.xor (if w.small child then hedgeCarrierResidualBit rich (restrictChild w.small w.child)
        ((w.smallCarrierDefectParityModel rich).eval unit) child else false)
        (hedgeForestParentBitsFrom rich w.smallOutcomeFlowSuccessor child parents)) (bits child) := by
  have mechanism := FiniteLatentSCM.withHedgeReadouts_mechanism_of_mem (w.smallCarrierDefectParityModel rich) rich
    (w.carrierFlowReadoutPlan rich noise) (HedgeCompensatedReadout.pivots_distinct w rich noise)
    (w.carrierFlowReadoutStep rich noise child) (HedgeCompensatedReadout.listed w rich noise child selected)
    bits unit parents
  exact (congrArg (hedgeIsSecond rich child) mechanism).trans
    (HedgeCompensatedReadout.small_response_bit w rich noise allowed unit child selected parents (bits child))

/-- The local large-flow equation holds in actual evaluation under any
intervention leaving this child free.  Its parents are the final responding
SCM values, not a coordinate sweep of the original observed assignment. -/
theorem HedgeWitness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_bit
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true) (free : intervention child = none) :
    let model := (w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
    let augmented := (w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
      (w.carrierFlowReadoutPlan rich noise) unit
    hedgeIsSecond rich child (model.evalUnder intervention augmented child) =
      Bool.xor (Bool.xor (if w.large child then hedgeCarrierResidualBit rich w.child
        ((w.largeCarrierDefectParityModel rich).eval unit) child else false)
        (hedgeForestParentBitsFrom rich w.largeOutcomeFlowSuccessor child
          (fun parent _edge => model.evalUnder intervention augmented parent))) (bits child) := by
  dsimp only
  change hedgeIsSecond rich child (FiniteLatentSCM.evalNodeUnder _ intervention _ child) = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [free]
  exact w.largeCarrierDefectParityModel_carrierFlowReadoutPlan_mechanism_bit rich noise bits unit child selected _

/-- The nested flow uses its own original residual and composed successor,
with the identical explicit fresh inputs.  Full observed alphabets and all
intervention values are allowed by the typed local equation. -/
theorem HedgeWitness.smallCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_bit
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (bits : Fin S.count -> Bool) (unit : (w.smallCarrierDefectParityModel rich).latent.Assignment)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true) (free : intervention child = none) :
    let model := (w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
    let augmented := (w.smallCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
      (w.carrierFlowReadoutPlan rich noise) unit
    hedgeIsSecond rich child (model.evalUnder intervention augmented child) =
      Bool.xor (Bool.xor (if w.small child then hedgeCarrierResidualBit rich (restrictChild w.small w.child)
        ((w.smallCarrierDefectParityModel rich).eval unit) child else false)
        (hedgeForestParentBitsFrom rich w.smallOutcomeFlowSuccessor child
          (fun parent _edge => model.evalUnder intervention augmented parent))) (bits child) := by
  dsimp only
  change hedgeIsSecond rich child (FiniteLatentSCM.evalNodeUnder _ intervention _ child) = _
  rw [FiniteLatentSCM.evalNodeUnder]
  unfold FiniteLatentSCM.equationUnder
  rw [free]
  exact w.smallCarrierDefectParityModel_carrierFlowReadoutPlan_mechanism_bit rich noise allowed bits unit child selected _

/-! ## Conserving the nested signal through all responding descendants -/

/-- The actual compensated nested model carries its original weighted
defect to the common outcome sinks, XORed with exactly the parity of all
new private inputs.  Every installed row is free under the original query
action.  Conservation includes all small-forest rows, not just route roots,
so removed old inputs and responding children cancel correctly.

This is a pointwise structural identity, uniform in the original latent
unit, fresh bits, forest size, routing merges, and full observed alphabets.
It does not assume fair defect/noise, identify a stand-alone signal with an
SCM, or yet integrate the independently weighted factors. -/
theorem HedgeWitness.smallCarrierDefectParityModel_carrierFlowReadoutPlan_sinkParity_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (bits : Fin S.count -> Bool) (unit : (w.smallCarrierDefectParityModel rich).latent.Assignment) :
    let model := (w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
    let augmented := (w.smallCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
      (w.carrierFlowReadoutPlan rich noise) unit
    hedgeNodeXor (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)
        (fun node => hedgeIsSecond rich node (model.evalUnder (hedgeDoSecond rich q.action) augmented node)) =
      Bool.xor (hedgeDefectBitOf G unit) (hedgeNodeXor w.smallOutcomeFlowNodes bits) := by
  let model := (w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
  let augmented := (w.smallCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
    (w.carrierFlowReadoutPlan rich noise) unit
  let flowBits := fun node => hedgeIsSecond rich node (model.evalUnder (hedgeDoSecond rich q.action) augmented node)
  let residual := hedgeCarrierResidualBit rich (restrictChild w.small w.child)
    ((w.smallCarrierDefectParityModel rich).eval unit)
  let source := fun node => Bool.xor (if w.small node then residual node else false) (bits node)
  have equations : forall node, w.smallOutcomeFlowNodes node = true ->
      flowBits node = Bool.xor (source node) (hedgeRoutingIncomingBits w.smallOutcomeFlowSuccessor flowBits node) := by
    intro node selected
    have notAction : q.action node = false := by
      have selectedUnion : w.rootReadoutNodes node = true ∨ w.small node = true := Bool.or_eq_true_iff.mp selected
      cases selectedUnion with
      | inl routed => exact w.rootReadoutNodes_avoids_action node routed
      | inr inside => exact w.small_avoids_intervention node inside
    have equation := w.smallCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_bit rich noise allowed bits unit
      (hedgeDoSecond rich q.action) node selected (hedgeDoSecond_of_false rich q.action notAction)
    have incoming := hedgeForestParentBitsFrom_eq_routingIncomingBits rich w.smallOutcomeFlowNodes
      w.smallOutcomeFlowSuccessor w.smallOutcomeFlowSuccessor_wellFormed
      (model.evalUnder (hedgeDoSecond rich q.action) augmented) node
    change flowBits node = Bool.xor (Bool.xor (if w.small node then residual node else false)
      (hedgeForestParentBitsFrom rich w.smallOutcomeFlowSuccessor node
        (fun parent _edge => model.evalUnder (hedgeDoSecond rich q.action) augmented parent))) (bits node) at equation
    rw [incoming] at equation
    have shuffle (value parents fresh : Bool) : Bool.xor (Bool.xor value parents) fresh =
        Bool.xor (Bool.xor value fresh) parents := by cases value <;> cases parents <;> cases fresh <;> rfl
    exact equation.trans (shuffle _ _ _)
  have conservation := hedgeRoutingFlow_conservation w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed source flowBits equations
  rw [w.smallOutcomeFlowSinks_eq_rootReadoutSinks] at conservation
  have sourceSum : hedgeNodeXor w.smallOutcomeFlowNodes source =
      Bool.xor (hedgeDefectBitOf G unit) (hedgeNodeXor w.smallOutcomeFlowNodes bits) := by
    change (NodeSet.members w.smallOutcomeFlowNodes).foldl
      (fun total node => Bool.xor total (Bool.xor (if w.small node then residual node else false) (bits node))) false = _
    rw [foldl_xor_pointwise]
    change Bool.xor (hedgeNodeXor w.smallOutcomeFlowNodes (fun node => if w.small node then residual node else false))
      (hedgeNodeXor w.smallOutcomeFlowNodes bits) = _
    rw [hedgeNodeXor_mask_of_subset w.small w.smallOutcomeFlowNodes
      (NodeSet.subset_union_right w.rootReadoutNodes w.small) residual]
    have correction : hedgeNodeXor w.small residual = hedgeDefectBitOf G unit :=
      (w.smallCarrierDefectBit_eq_inner rich ((w.smallCarrierDefectParityModel rich).eval unit)).symm.trans
        (w.smallCarrierDefectBitOf_eval rich unit).symm
    rw [correction]
  exact conservation.trans sourceSum

end Causality
end Thesis
