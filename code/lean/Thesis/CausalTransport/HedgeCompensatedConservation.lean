import Thesis.CausalTransport.HedgeReadoutPreservation

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}}

/-!
# Conserving the original large-carrier signal through compensated routing

The nested compensated flow has no action vertices, so its sink signal is
the weighted defect plus the fresh private parity.  The large flow requires
a different argument: intervening cuts some original forest equations.
Their effective sources are the fixed output bits with incoming parity
cancelled, not their original exogenous residuals.

Permitted routes avoid the outer-only forest.  Every kept parent of an
outer-only vertex is itself outer-only, so the complete values at those
vertices remain unchanged under arbitrary interventions.  The prioritized
flow also retains exactly their old incoming kept edges.  In particular,
cut outer-only rows retain their original effective source, including when
the action has several vertices or contains a non-sink kept parent.

At installed free rows, the compensated mechanism supplies the original
residual and one fresh bit.  Outside the large forest no old source is embedded.
Comparing effective sources on the full composed flow and applying finite
forest conservation therefore proves that its common outcome-sink parity
is the original large-carrier root signal XOR all new private bits.

The main theorem allows every intervention that leaves the installed rows
free, with arbitrary full value labels at intervened outer-only vertices.
The original query's `do(second)` action is a corollary.  No non-influence,
kept-sink, singleton-action, or noise-weight premise is assumed.  These are
actual pointwise SCM identities, not an assumed equality of independent noisy
signal records.  `HedgeCompensatedCounterexample` separately integrates the
real fresh factors and packages positive original-query countermodels on the
permitted routes.
-/

namespace HedgeCompensatedConservation

variable {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## Protected outer-only vertices and their incoming kept edges -/

private theorem outer_not_readout (w : HedgeWitness G q)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (child : Fin S.count) (inside : w.large child = true) (outside : w.small child = false) :
    w.rootReadoutNodes child = false := by
  apply Bool.eq_false_iff.mpr
  intro routed
  cases allowed child routed with
  | inl small => rw [small] at outside; cases outside
  | inr absent => rw [absent] at inside; cases inside

private theorem outer_not_installed (w : HedgeWitness G q)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (child : Fin S.count) (inside : w.large child = true) (outside : w.small child = false) :
    w.smallOutcomeFlowNodes child = false := by
  simp only [HedgeWitness.smallOutcomeFlowNodes, NodeSet.union,
    outer_not_readout w allowed child inside outside, outside, Bool.or_false]

private theorem kept_parent_outer (w : HedgeWitness G q)
    (parent child : Fin S.count) (outside : w.small child = false) (keptAt : w.child parent = some child) :
    w.large parent = true ∧ w.small parent = false := by
  refine ⟨(w.large_forest.child_edge parent child keptAt).1, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro selected
  have restricted : restrictChild w.small w.child parent = some child := by
    simpa only [restrictChild, selected, if_true] using keptAt
  have childInside := (w.small_forest.child_edge parent child restricted).2.1
  rw [outside] at childInside
  cases childInside

/-- Neither a retained route edge nor an old route-parent edge can enter
an outer-only child.  Thus priority changes no incoming incidence at this
row, even if the ambient graph has extra non-kept arrows into it. -/
private theorem same_incoming_outer (w : HedgeWitness G q)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (child : Fin S.count) (inside : w.large child = true) (outside : w.small child = false) :
    forall parent, w.largeOutcomeFlowSuccessor parent = some child ↔ w.child parent = some child := by
  intro parent
  have childNotReadout := outer_not_readout w allowed child inside outside
  cases routed : w.rootReadoutNodes parent with
  | false => simp only [HedgeWitness.largeOutcomeFlowSuccessor, forestChildPrioritize, routed,
      Bool.false_eq_true, if_false]
  | true =>
      have noOld : w.child parent ≠ some child := by
        intro found
        have parentOuter := kept_parent_outer w parent child outside found
        have notReadout := outer_not_readout w allowed parent parentOuter.1 parentOuter.2
        rw [notReadout] at routed
        cases routed
      have noNew : w.rootReadoutSuccessor parent ≠ some child := by
        intro found
        have childReadout := (w.rootReadoutSuccessor_nodes found).2
        rw [childNotReadout] at childReadout
        cases childReadout
      simp only [HedgeWitness.largeOutcomeFlowSuccessor, forestChildPrioritize, routed, if_true]
      exact ⟨fun found => False.elim (noNew found), fun found => False.elim (noOld found)⟩

/-- Full values at protected vertices remain unchanged, not just their
parity bits.  The general mechanism-closure theorem now supplies this
specialization; the finite fold protects every row outside its installed
mask, so this argument need not duplicate the topological recursion. -/
private theorem outer_evalNode_eq (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (child : Fin S.count) (inside : w.large child = true) (outside : w.small child = false) :
    ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).evalNodeUnder
        intervention ((w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
          (w.carrierFlowReadoutPlan rich noise) unit) child =
      (w.largeCarrierDefectParityModel rich).evalNodeUnder intervention unit child := by
  apply w.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_eq_of_protected rich noise allowed
    intervention bits unit child
  simp only [HedgeWitness.carrierFlowProtectedNodes, outer_not_installed w allowed child inside outside, Bool.not_false]

/-! ## Comparing effective sources, including cut structural equations -/

private theorem incoming_outer_eq (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (child : Fin S.count) (inside : w.large child = true) (outside : w.small child = false) :
    let oldSample := (w.largeCarrierDefectParityModel rich).evalUnder intervention unit
    let newSample := ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich
      (w.carrierFlowReadoutPlan rich noise)).evalUnder intervention
        ((w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits (w.carrierFlowReadoutPlan rich noise) unit)
    hedgeRoutingIncomingBits w.largeOutcomeFlowSuccessor (fun node => hedgeIsSecond rich node (newSample node)) child =
      hedgeRoutingIncomingBits w.child (fun node => hedgeIsSecond rich node (oldSample node)) child := by
  dsimp only
  rw [← hedgeForestParentBitsFrom_eq_routingIncomingBits rich w.largeOutcomeFlowNodes
    w.largeOutcomeFlowSuccessor w.largeOutcomeFlowSuccessor_wellFormed _ child]
  rw [hedgeForestParentBitsFrom_congr_to_child rich child w.largeOutcomeFlowSuccessor w.child _
    (same_incoming_outer w allowed child inside outside)]
  refine (hedgeForestParentBitsFrom_congr_of_kept rich w.child child _ _ ?_).trans
    (hedgeForestParentBitsFrom_eq_routingIncomingBits rich w.large w.child w.large_forest.wellFormedBool _ child)
  intro parent _edge keptAt
  have parentOuter := kept_parent_outer w parent child outside keptAt
  exact congrArg (hedgeIsSecond rich parent)
    (outer_evalNode_eq w rich noise allowed bits unit intervention parent parentOuter.1 parentOuter.2)

private theorem old_localSource_free (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (child : Fin S.count) (inside : w.large child = true) (free : intervention child = none) :
    hedgeRoutingLocalSource w.child
        (fun node => hedgeIsSecond rich node ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit node)) child =
      hedgeCarrierResidualBit rich w.child ((w.largeCarrierDefectParityModel rich).eval unit) child := by
  have equation := w.largeCarrierDefectParityModel_evalUnder_residual_bit rich unit intervention child inside free
  rw [hedgeForestParentBitsFrom_eq_routingIncomingBits rich w.large w.child w.large_forest.wellFormedBool _ child]
    at equation
  unfold hedgeRoutingLocalSource
  dsimp only
  rw [equation]
  have cancel (source incoming : Bool) : Bool.xor (Bool.xor source incoming) incoming = source := by
    cases source <;> cases incoming <;> rfl
  exact cancel _ _

private theorem new_localSource_installed (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (child : Fin S.count) (selected : w.smallOutcomeFlowNodes child = true) (free : intervention child = none) :
    let model := (w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
    let augmented := (w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
      (w.carrierFlowReadoutPlan rich noise) unit
    hedgeRoutingLocalSource w.largeOutcomeFlowSuccessor
        (fun node => hedgeIsSecond rich node (model.evalUnder intervention augmented node)) child =
      Bool.xor (if w.large child then hedgeCarrierResidualBit rich w.child
        ((w.largeCarrierDefectParityModel rich).eval unit) child else false) (bits child) := by
  dsimp only
  have equation := w.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_bit rich noise bits unit
    intervention child selected free
  dsimp only at equation
  rw [hedgeForestParentBitsFrom_eq_routingIncomingBits rich w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
    w.largeOutcomeFlowSuccessor_wellFormed _ child] at equation
  unfold hedgeRoutingLocalSource
  dsimp only
  rw [equation]
  have cancel (source incoming fresh : Bool) :
      Bool.xor (Bool.xor (Bool.xor source incoming) fresh) incoming = Bool.xor source fresh := by
    cases source <;> cases incoming <;> cases fresh <;> rfl
  exact cancel _ _ _

/-- Off the installed rows, membership in the large flow means this is
an outer-only original forest vertex, not an outside routing vertex. -/
private theorem outer_of_flow_of_not_installed (w : HedgeWitness G q)
    (child : Fin S.count) (selected : w.largeOutcomeFlowNodes child = true)
    (notInstalled : w.smallOutcomeFlowNodes child = false) :
    w.large child = true ∧ w.small child = false := by
  have notReadout : w.rootReadoutNodes child = false := by
    apply Bool.eq_false_iff.mpr
    intro routed
    have inSmallFlow : w.smallOutcomeFlowNodes child = true := NodeSet.subset_union_left w.rootReadoutNodes w.small child routed
    rw [notInstalled] at inSmallFlow
    cases inSmallFlow
  have outside : w.small child = false := by
    apply Bool.eq_false_iff.mpr
    intro inside
    have inSmallFlow : w.smallOutcomeFlowNodes child = true := NodeSet.subset_union_right w.rootReadoutNodes w.small child inside
    rw [notInstalled] at inSmallFlow
    cases inSmallFlow
  have inside : w.large child = true := by
    simpa only [HedgeWitness.largeOutcomeFlowNodes, NodeSet.union, notReadout, Bool.false_or] using selected
  exact ⟨inside, outside⟩

/-- A cut outer-only row is covered by the same equality as a free one:
its fixed full output and every effective incoming contribution agree. -/
private theorem source_comparison (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (free : forall node, w.smallOutcomeFlowNodes node = true -> intervention node = none)
    (child : Fin S.count) (selected : w.largeOutcomeFlowNodes child = true) :
    let oldBits := fun node => hedgeIsSecond rich node ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit node)
    let newBits := fun node => hedgeIsSecond rich node
      (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).evalUnder
        intervention ((w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
          (w.carrierFlowReadoutPlan rich noise) unit) node)
    hedgeRoutingLocalSource w.largeOutcomeFlowSuccessor newBits child =
      Bool.xor (if w.large child then hedgeRoutingLocalSource w.child oldBits child else false)
        (if w.smallOutcomeFlowNodes child then bits child else false) := by
  dsimp only
  by_cases installed : w.smallOutcomeFlowNodes child = true
  · rw [if_pos installed]
    have freshSource := new_localSource_installed w rich noise bits unit intervention child installed (free child installed)
    by_cases inside : w.large child = true
    · rw [if_pos inside] at freshSource ⊢
      exact freshSource.trans (congrArg (fun source => Bool.xor source (bits child))
        (old_localSource_free w rich unit intervention child inside (free child installed)).symm)
    · simpa only [if_neg inside] using freshSource
  · have outsideInstalled : w.smallOutcomeFlowNodes child = false := Bool.eq_false_iff.mpr installed
    have outer := outer_of_flow_of_not_installed w child selected outsideInstalled
    simp only [if_neg installed, if_pos outer.1, Bool.xor_false]
    unfold hedgeRoutingLocalSource
    rw [incoming_outer_eq w rich noise allowed bits unit intervention child outer.1 outer.2]
    exact congrArg (fun value => Bool.xor (hedgeIsSecond rich child value) _)
      (outer_evalNode_eq w rich noise allowed bits unit intervention child outer.1 outer.2)

private theorem small_flow_subset_large (w : HedgeWitness G q) :
    NodeSet.Subset w.smallOutcomeFlowNodes w.largeOutcomeFlowNodes := by
  intro child selected
  have selectedUnion : w.rootReadoutNodes child = true ∨ w.small child = true := Bool.or_eq_true_iff.mp selected
  cases selectedUnion with
  | inl routed => exact NodeSet.subset_union_left w.rootReadoutNodes w.large child routed
  | inr inside => exact NodeSet.subset_union_right w.rootReadoutNodes w.large child (w.small_subset_large child inside)

private theorem original_sinks (w : HedgeWitness G q) : keptSinks w.large w.child = w.roots := by
  funext node
  apply Bool.eq_iff_iff.mpr
  exact (keptSinks_iff w.large w.child node).trans (w.large_forest.roots_exact node).symm

end HedgeCompensatedConservation

/-! ## Full structural transport of the original root signal -/

/-- Compensated routing leaves every outer-only full value unchanged under
arbitrary interventions.  It does not require those vertices to be sinks,
nor does it restrict intervention labels to the two distinguished values. -/
theorem HedgeWitness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_evalUnder_eq_of_outer
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (child : Fin S.count) (inside : w.large child = true) (outside : w.small child = false) :
    ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).evalUnder
        intervention ((w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
          (w.carrierFlowReadoutPlan rich noise) unit) child =
      (w.largeCarrierDefectParityModel rich).evalUnder intervention unit child :=
  HedgeCompensatedConservation.outer_evalNode_eq w rich noise allowed bits unit intervention child inside outside

/-- The whole large carrier's original root signal reaches the common
outcome sinks with exactly the parity of the new private inputs added.
All original action-cut contributions are retained by effective-source
comparison, so composite interventions and non-sink intervened vertices
need no extra hypothesis beyond keeping installed rows free.

The identity is pointwise in the real old latent unit and encoded fresh bits.
Weights, support, and bias are not assumed here; integrating the actual
independent factors and proving probability separation is a separate step. -/
theorem HedgeWitness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_sinkParity_evalUnder
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment)
    (intervention : (node : Fin S.count) -> Option (S.Value node))
    (free : forall node, w.smallOutcomeFlowNodes node = true -> intervention node = none) :
    let model := (w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
    let augmented := (w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
      (w.carrierFlowReadoutPlan rich noise) unit
    hedgeNodeXor (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)
        (fun node => hedgeIsSecond rich node (model.evalUnder intervention augmented node)) =
      Bool.xor (hedgeRootParityEvent rich w.roots ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit))
        (hedgeNodeXor w.smallOutcomeFlowNodes bits) := by
  let oldBits := fun node => hedgeIsSecond rich node ((w.largeCarrierDefectParityModel rich).evalUnder intervention unit node)
  let newBits := fun node => hedgeIsSecond rich node
    (((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)).evalUnder
      intervention ((w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
        (w.carrierFlowReadoutPlan rich noise) unit) node)
  let oldSource := hedgeRoutingLocalSource w.child oldBits
  let newSource := hedgeRoutingLocalSource w.largeOutcomeFlowSuccessor newBits
  have conservation := hedgeRoutingFlow_conservation_localSource w.largeOutcomeFlowNodes w.largeOutcomeFlowSuccessor
    w.largeOutcomeFlowSuccessor_wellFormed newBits
  rw [w.largeOutcomeFlowSinks_eq_rootReadoutSinks] at conservation
  have oldConservation := hedgeRoutingFlow_conservation_localSource w.large w.child w.large_forest.wellFormedBool oldBits
  rw [HedgeCompensatedConservation.original_sinks w] at oldConservation
  have sourceSum : hedgeNodeXor w.largeOutcomeFlowNodes newSource =
      Bool.xor (hedgeNodeXor w.large oldSource) (hedgeNodeXor w.smallOutcomeFlowNodes bits) := by
    have rewriteSources : hedgeNodeXor w.largeOutcomeFlowNodes newSource =
        hedgeNodeXor w.largeOutcomeFlowNodes (fun node =>
          Bool.xor (if w.large node then oldSource node else false)
            (if w.smallOutcomeFlowNodes node then bits node else false)) := by
      unfold hedgeNodeXor
      apply foldl_congr_of_mem
      intro total node member
      exact congrArg (Bool.xor total) (HedgeCompensatedConservation.source_comparison w rich noise allowed bits unit
        intervention free node ((NodeSet.mem_members_iff w.largeOutcomeFlowNodes node).mp member))
    rw [rewriteSources]
    unfold hedgeNodeXor
    rw [foldl_xor_pointwise]
    change Bool.xor (hedgeNodeXor w.largeOutcomeFlowNodes (fun node => if w.large node then oldSource node else false))
      (hedgeNodeXor w.largeOutcomeFlowNodes (fun node => if w.smallOutcomeFlowNodes node then bits node else false)) = _
    rw [hedgeNodeXor_mask_of_subset w.large w.largeOutcomeFlowNodes (NodeSet.subset_union_right w.rootReadoutNodes w.large),
      hedgeNodeXor_mask_of_subset w.smallOutcomeFlowNodes w.largeOutcomeFlowNodes
        (HedgeCompensatedConservation.small_flow_subset_large w)]
    rfl
  exact conservation.trans (sourceSum.trans
    (congrArg (fun source => Bool.xor source (hedgeNodeXor w.smallOutcomeFlowNodes bits)) oldConservation.symm))

/-- The original hedge action automatically leaves every compensated row
free.  Hence no caller-supplied action/sink condition is needed to transport
the large model's original `do(second)` root event to queried outcome sinks. -/
theorem HedgeWitness.largeCarrierDefectParityModel_carrierFlowReadoutPlan_sinkParity_doSecond
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S) (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true -> w.small node = true ∨ w.large node = false)
    (bits : Fin S.count -> Bool) (unit : (w.largeCarrierDefectParityModel rich).latent.Assignment) :
    let model := (w.largeCarrierDefectParityModel rich).withHedgeReadouts rich (w.carrierFlowReadoutPlan rich noise)
    let augmented := (w.largeCarrierDefectParityModel rich).hedgeReadoutAssignment rich bits
      (w.carrierFlowReadoutPlan rich noise) unit
    hedgeNodeXor (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor)
        (fun node => hedgeIsSecond rich node (model.evalUnder (hedgeDoSecond rich q.action) augmented node)) =
      Bool.xor (hedgeRootParityEvent rich w.roots
        ((w.largeCarrierDefectParityModel rich).evalUnder (hedgeDoSecond rich q.action) unit))
        (hedgeNodeXor w.smallOutcomeFlowNodes bits) := by
  apply w.largeCarrierDefectParityModel_carrierFlowReadoutPlan_sinkParity_evalUnder rich noise allowed bits unit
  intro node selected
  have notAction : q.action node = false := by
    have selectedUnion : w.rootReadoutNodes node = true ∨ w.small node = true := Bool.or_eq_true_iff.mp selected
    cases selectedUnion with
    | inl routed => exact w.rootReadoutNodes_avoids_action node routed
    | inr inside => exact w.small_avoids_intervention node inside
  exact hedgeDoSecond_of_false rich q.action notAction

end Causality
end Thesis
