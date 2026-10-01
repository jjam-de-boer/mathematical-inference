import Thesis.Causality.PrivateNoiseClosure
import Thesis.CausalTransport.HedgeCompensatedReadout

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Protected marginals through finite responding readout plans

The older off-plan theorem assumes that every other mechanism ignores each
readout pivot.  Compensated carrier plans deliberately include internal
vertices with responding children, so that global condition is unavailable.
Only the inspected marginal needs protection: its rows must use protected
parent values and no instruction may replace a protected row.

`PrivateNoiseClosure` transports this local mechanism invariant through any
private replacement.  The finite fold below therefore needs no ordering,
distinct pivots, kept-sink condition, or non-influence of unprotected rows.
It integrates every actual new factor, even for repeated instructions.

For the compensated carriers, all coordinates outside the installed mask
are protected.  Outer-only rows read only outer-only kept parents; unmodified
outside-large rows ignore parents.  Thus a conditioning set may lie inside
the large forest while retaining its exact interventional denominator.  The
root-omitted carrier marginal theorem matches those original denominators
in the same pair.  This is preparation for conditional countermodels, not a
claim that conditioners on the installed rows have already been handled.
-/

/-! ## Local protection survives an arbitrary finite fold -/

/-- Unprotected readouts preserve closure of the protected rows, in any
order and with arbitrary repeated pivots and replacement signals. -/
theorem FiniteLatentSCM.withHedgeReadouts_mechanismsClosedOn
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (closed : base.MechanismsClosedOn nodes)
    (steps : List (HedgeReadoutStep S)) (off : forall step, step ∈ steps -> nodes step.pivot = false) :
    (base.withHedgeReadouts rich steps).MechanismsClosedOn nodes := by
  induction steps generalizing base with
  | nil => exact closed
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis (step.apply rich base)
        (base.withPrivateBooleanNoise_mechanismsClosedOn nodes closed step.pivot (off step List.mem_cons_self) step.noise _)
        (fun next listed => off next (List.mem_cons_of_mem _ listed))

/-- Full protected values agree for every represented old unit and bit
family.  The companion probability theorem integrates successive real
factors directly, so it also includes independent inputs at repeated pivots
which a node-indexed family alone would not represent exhaustively. -/
theorem FiniteLatentSCM.withHedgeReadouts_evalUnder_eq_of_mechanismsClosedOn
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (closed : base.MechanismsClosedOn nodes)
    (steps : List (HedgeReadoutStep S)) (off : forall step, step ∈ steps -> nodes step.pivot = false)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (bits : Fin S.count -> Bool) (unit : base.latent.Assignment)
    (child : Fin S.count) (selected : nodes child = true) :
    (base.withHedgeReadouts rich steps).evalUnder intervention (base.hedgeReadoutAssignment rich bits steps unit) child =
      base.evalUnder intervention unit child := by
  induction steps generalizing base with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      have closedNext := base.withPrivateBooleanNoise_mechanismsClosedOn nodes closed step.pivot
        (off step List.mem_cons_self) step.noise
        (fun parents inputs bit => hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal parents
          (base.mechanism step.pivot parents inputs) bit)
      have tail := inductionHypothesis (step.apply rich base) closedNext
        (fun next listed => off next (List.mem_cons_of_mem _ listed))
        (PrivateBooleanNoise.assignment base.latent (bits step.pivot) unit)
      exact tail.trans (base.withPrivateBooleanNoise_evalNodeUnder_eq_of_mechanismsClosedOn nodes closed step.pivot
        (off step List.mem_cons_self) step.noise
        (fun parents inputs bit => hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal parents
          (base.mechanism step.pivot parents inputs) bit)
        intervention unit (bits step.pivot) child selected)

/-- Every protected interventional event keeps its original probability.
The induction integrates one literal private factor at each stage and
transports closure to the next stage.  No common latent coupling, ordering,
support, or bias premise is used. -/
theorem FiniteLatentSCM.withHedgeReadouts_interventionalValue_equiv_of_mechanismsClosedOn
    (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (closed : base.MechanismsClosedOn nodes)
    (steps : List (HedgeReadoutStep S)) (off : forall step, step ∈ steps -> nodes step.pivot = false)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (event : S.Assignment -> Bool) (eventLocal : EventDependsOnlyOn nodes event) :
    QProb.Equiv ((base.withHedgeReadouts rich steps).interventionalValue intervention event)
      (base.interventionalValue intervention event) := by
  induction steps generalizing base with
  | nil => exact QProb.equiv_refl _
  | cons step rest inductionHypothesis =>
      have closedNext := base.withPrivateBooleanNoise_mechanismsClosedOn nodes closed step.pivot
        (off step List.mem_cons_self) step.noise
        (fun parents inputs bit => hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal parents
          (base.mechanism step.pivot parents inputs) bit)
      have tail := inductionHypothesis (step.apply rich base) closedNext
        (fun next listed => off next (List.mem_cons_of_mem _ listed))
      have head := base.withPrivateBooleanNoise_interventionalValue_equiv_of_mechanismsClosedOn nodes closed step.pivot
        (off step List.mem_cons_self) step.noise
        (fun parents inputs bit => hedgeNoisyReadout rich step.pivot step.injectOld step.parentSignal parents
          (base.mechanism step.pivot parents inputs) bit)
        intervention event eventLocal
      exact QProb.equiv_trans tail head

/-- A joint kernel inspecting protected coordinates is unchanged by the
whole plan.  Both empty-action observational semantics and nonempty-action
interventional semantics are included at every reference assignment. -/
theorem JointKernelQuery.withHedgeReadouts_valueEquivalent_of_mechanismsClosedOn
    (query : JointKernelQuery S) (base : ExactModel S) (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (closed : base.MechanismsClosedOn nodes)
    (steps : List (HedgeReadoutStep S)) (off : forall step, step ∈ steps -> nodes step.pivot = false)
    (outcomeProtected : NodeSet.Subset query.outcome nodes) :
    query.ValueEquivalent (base.withHedgeReadouts rich steps) base := by
  intro reference
  let updated := base.withHedgeReadouts rich steps
  let kernel := query.operationKernel
  let event := Kernel.agreesOn query.outcome reference
  have eventLocal : EventDependsOnlyOn nodes event := by
    intro first second agree
    exact Kernel.agreesOn_sample_congr query.outcome reference first second
      (fun child selected => agree child (outcomeProtected child selected))
  have preserved (intervention : (node : Fin S.count) -> Option (S.Value node)) :
      QProb.Equiv (updated.interventionalValue intervention event) (base.interventionalValue intervention event) :=
    base.withHedgeReadouts_interventionalValue_equiv_of_mechanismsClosedOn rich nodes closed steps off
      intervention event eventLocal
  have cylinderEqual : QProb.Equiv ((kernel.distribution updated reference).probVal event)
      ((kernel.distribution base reference).probVal event) := by
    unfold Kernel.distribution
    split
    · exact preserved (kernel.intervention reference)
    · exact preserved (FiniteLatentSCM.noIntervention S)
  exact ⟨ProbabilityResult.trans (Kernel.unconditionalDenote updated query.outcome query.action reference)
    (ProbabilityResult.trans (.value cylinderEqual)
      (ProbabilityResult.symm (Kernel.unconditionalDenote base query.outcome query.action reference)))⟩

/-! ## The carriers' protected set includes outer-only vertices -/

/-- Exactly the coordinates absent from the compensated installation mask.
The set includes outer-only vertices and unmodified outside-large vertices,
not merely coordinates that precede every readout in the ambient order. -/
def HedgeWitness.carrierFlowProtectedNodes {G : ObservedGraph S} {q : JointKernelQuery S}
    (w : HedgeWitness G q) : NodeSet S := fun node => !(w.smallOutcomeFlowNodes node)

namespace HedgeReadoutPreservation

variable {G : ObservedGraph S} {q : JointKernelQuery S}

private theorem protected_not_small (w : HedgeWitness G q) (child : Fin S.count)
    (selected : w.carrierFlowProtectedNodes child = true) : w.small child = false := by
  apply Bool.eq_false_iff.mpr
  intro inside
  have installed : w.smallOutcomeFlowNodes child = true := NodeSet.subset_union_right w.rootReadoutNodes w.small child inside
  change Bool.not (w.smallOutcomeFlowNodes child) = true at selected
  rw [installed] at selected
  cases selected

/-- A kept input into a protected row is itself outer-only and protected.
Small-forest closure excludes small parents; permitted routes exclude any
remaining original large parent from the installation mask. -/
private theorem kept_parent_protected (w : HedgeWitness G q)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (child : Fin S.count) (selected : w.carrierFlowProtectedNodes child = true)
    (parent : Fin S.count) (found : w.child parent = some child) : w.carrierFlowProtectedNodes parent = true := by
  have parentLarge := (w.large_forest.child_edge parent child found).1
  have childOutside := protected_not_small w child selected
  have parentOutside : w.small parent = false := by
    apply Bool.eq_false_iff.mpr
    intro inside
    have restricted : restrictChild w.small w.child parent = some child := by simpa only [restrictChild, inside, if_true] using found
    have childInside := (w.small_forest.child_edge parent child restricted).2.1
    rw [childOutside] at childInside
    cases childInside
  have notRouted : w.rootReadoutNodes parent = false := by
    apply Bool.eq_false_iff.mpr
    intro routed
    cases allowed parent routed with
    | inl small => rw [parentOutside] at small; cases small
    | inr outside => rw [parentLarge] at outside; cases outside
  simp only [HedgeWitness.carrierFlowProtectedNodes, HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
    notRouted, parentOutside, Bool.false_or, Bool.not_false]

private theorem plan_off_protected (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) :
    forall step, step ∈ w.carrierFlowReadoutPlan rich noise -> w.carrierFlowProtectedNodes step.pivot = false := by
  intro step listed
  rcases List.mem_map.mp listed with ⟨node, member, same⟩
  subst step
  have installed := (NodeSet.mem_members_iff w.smallOutcomeFlowNodes node).mp member
  simp only [HedgeWitness.carrierFlowProtectedNodes, HedgeWitness.carrierFlowReadoutStep, installed, Bool.not_true]

end HedgeReadoutPreservation

/-- The large carrier's protected rows read only protected kept parents.
The carrier wrapper preserves this property at every typed latent input and
full value, without selecting a global latent extension from an existential. -/
theorem HedgeWitness.largeCarrierDefectParityModel_mechanismsClosedOn_carrierFlowProtectedNodes
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false) :
    (w.largeCarrierDefectParityModel rich).MechanismsClosedOn w.carrierFlowProtectedNodes := by
  intro child selected first second inputs agree
  have parentEqual : hedgeForestParentBitsFrom rich w.child child first = hedgeForestParentBitsFrom rich w.child child second := by
    apply hedgeForestParentBitsFrom_congr_of_kept
    intro parent edge found
    exact congrArg (hedgeIsSecond rich parent)
      (agree parent edge (HedgeReadoutPreservation.kept_parent_protected w allowed child selected parent found))
  have oldEqual (oldInputs : (hedgeLatentExtension G).Inputs child) :
      (w.largeParityModel rich).mechanism child first oldInputs = (w.largeParityModel rich).mechanism child second oldInputs := by
    simp only [HedgeWitness.largeParityModel, hedgeForestParityModel, hedgeForestParityOutput]
    rw [parentEqual]
  dsimp only [HedgeWitness.largeCarrierDefectParityModel, hedgeCarrierDefectModel]
  rw [oldEqual]

/-- At a protected row the nested mechanism is exactly the large mechanism:
the row lies outside `small`, and both wrappers retain the same latent inputs.
Consequently the same local closure proof applies to the nested carrier. -/
theorem HedgeWitness.smallCarrierDefectParityModel_mechanismsClosedOn_carrierFlowProtectedNodes
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false) :
    (w.smallCarrierDefectParityModel rich).MechanismsClosedOn w.carrierFlowProtectedNodes := by
  intro child selected first second inputs agree
  have outside := HedgeReadoutPreservation.protected_not_small w child selected
  have same (parents : S.ParentValues child) :
      (w.smallCarrierDefectParityModel rich).mechanism child parents inputs =
        (w.largeCarrierDefectParityModel rich).mechanism child parents inputs := by
    dsimp only [HedgeWitness.smallCarrierDefectParityModel, HedgeWitness.largeCarrierDefectParityModel, hedgeCarrierDefectModel]
    rw [← w.parityMechanism_eq_of_not_small rich child parents _ outside]
  exact (same first).trans
    ((w.largeCarrierDefectParityModel_mechanismsClosedOn_carrierFlowProtectedNodes rich allowed child selected first second inputs agree).trans
      (same second).symm)

/-! ## Full value and denominator preservation in the actual carrier pair -/

/-- The large carrier retains the entire old value at every protected row,
under arbitrary interventions and every represented fresh input family. -/
theorem HedgeWitness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_eq_of_protected
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (child : Fin S.count) (selected : w.carrierFlowProtectedNodes child = true) :
    ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention
        ((w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit) child =
      (w.largeCarrierDefectParityModel rich).evalUnder intervention unit child :=
  FiniteLatentSCM.withHedgeReadouts_evalUnder_eq_of_mechanismsClosedOn _ rich w.carrierFlowProtectedNodes
    (w.largeCarrierDefectParityModel_mechanismsClosedOn_carrierFlowProtectedNodes rich allowed) _
    (HedgeReadoutPreservation.plan_off_protected w rich noise) intervention bits unit child selected

/-- The nested carrier has the same full-value preservation property,
including free outer-only rows which respond to other protected parents. -/
theorem HedgeWitness.smallCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_eq_of_protected
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (bits : Fin S.count -> Bool) (unit : (w.smallCarrierDefectParityModel rich).latent.Assignment)
    (child : Fin S.count) (selected : w.carrierFlowProtectedNodes child = true) :
    ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention
        ((w.smallCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit) child =
      (w.smallCarrierDefectParityModel rich).evalUnder intervention unit child :=
  FiniteLatentSCM.withHedgeReadouts_evalUnder_eq_of_mechanismsClosedOn _ rich w.carrierFlowProtectedNodes
    (w.smallCarrierDefectParityModel_mechanismsClosedOn_carrierFlowProtectedNodes rich allowed) _
    (HedgeReadoutPreservation.plan_off_protected w rich noise) intervention bits unit child selected

/-- Every kernel on protected coordinates has the same value in the two
actual compensated SCMs.  The original root-omitted marginal theorem supplies
base equality; separate finite-factor preservation retains that denominator
on both sides.  Its action is arbitrary and may be empty. -/
theorem HedgeWitness.carrierDefectParityModels_carrierFlowReadoutPlan_valueEquivalent_of_protected
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (query : JointKernelQuery S) (outcomeProtected : NodeSet.Subset query.outcome w.carrierFlowProtectedNodes) :
    query.ValueEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise))
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)) := by
  have rootOmitted : query.outcome w.actionRoot = false := by
    apply Bool.eq_false_iff.mpr
    intro selected
    have protectedRoot := outcomeProtected w.actionRoot selected
    have installed : w.smallOutcomeFlowNodes w.actionRoot = true :=
      NodeSet.subset_union_right w.rootReadoutNodes w.small w.actionRoot w.actionRoot_in_small
    change Bool.not (w.smallOutcomeFlowNodes w.actionRoot) = true at protectedRoot
    rw [installed] at protectedRoot
    cases protectedRoot
  have baseEqual := w.carrierDefectParityModels_valueEquivalent_of_rootOmitted rich w.actionRoot
    w.actionRoot_in_roots query rootOmitted
  have leftPreserved := query.withHedgeReadouts_valueEquivalent_of_mechanismsClosedOn (w.largeCarrierDefectParityModel rich)
    rich w.carrierFlowProtectedNodes (w.largeCarrierDefectParityModel_mechanismsClosedOn_carrierFlowProtectedNodes rich allowed)
    _ (HedgeReadoutPreservation.plan_off_protected w rich noise) outcomeProtected
  have rightPreserved := query.withHedgeReadouts_valueEquivalent_of_mechanismsClosedOn (w.smallCarrierDefectParityModel rich)
    rich w.carrierFlowProtectedNodes (w.smallCarrierDefectParityModel_mechanismsClosedOn_carrierFlowProtectedNodes rich allowed)
    _ (HedgeReadoutPreservation.plan_off_protected w rich noise) outcomeProtected
  intro reference
  rcases leftPreserved reference with ⟨leftEqual⟩
  rcases baseEqual reference with ⟨oldEqual⟩
  rcases rightPreserved reference with ⟨rightEqual⟩
  exact ⟨ProbabilityResult.trans leftEqual (ProbabilityResult.trans oldEqual (ProbabilityResult.symm rightEqual))⟩

end Causality
end Thesis
