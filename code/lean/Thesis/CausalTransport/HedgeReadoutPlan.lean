import Thesis.CausalTransport.HedgeRoutedCounterexample
import Thesis.CausalTransport.HedgeCarrierReplayPlan

namespace Thesis
namespace Causality

open Probability

/-!
# Constructing readout plans from a finite routing forest

The countermodel assembler accepts an explicit linear plan and its pure
outcome-to-root substitution identity.  This module constructs that plan
automatically from a well-formed no-splitting successor map.  Selected
vertices are processed in the signature's existing topological order; each
instruction injects its old bit exactly at a selected source and XORs every
routed parent.  Noise records may vary independently by vertex.

The zero-bit observable sweep satisfies all local flow equations.  Finite
forest conservation therefore proves the final sink event's pullback to
the complete source parity, including merging paths and multiple sinks.
Zero bits are used only for this combinatorial identity: the actual SCM
construction retains positive biased private noise at every updated vertex.

The hedge specialization uses its already constructed canonical all-root
routing forest.  Its remaining semantic hypothesis is stated explicitly:
the countermodel constructor still requires every route vertex to be a sink
of the original kept c-forest map.  Its interventional pullback uses that
condition.  A separate observational theorem below now permits routes to
re-enter the small forest at internal vertices: the retained-state replay
includes responding descendants.  Outer-only route updates and a general
interventional routing identity are not hidden in the generated plan.
-/

variable {S : ObservedSignature.{0}}

namespace HedgeRoutingReadoutPlan

/-- All parents sent to `child` by the selected successor map, enumerated
constructively in the observed signature's topological order. -/
def parentNodes (successor : ForestChild S) (child : Fin S.count) : List (Fin S.count) :=
  (List.finRange S.count).filter (fun parent => decide (successor parent = some child))

/-- One generated linear instruction.  Its edge proofs come from the
computed well-formedness certificate, so an undeclared parent cannot enter
the readout mechanism. -/
def step (nodes sources : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (child : Fin S.count) :
    HedgeLinearReadoutStep S where
  pivot := child
  noise := noise child
  injectOld := sources child
  parents := parentNodes successor child
  parent_edges := by
    intro parent listed
    have selected : successor parent = some child := of_decide_eq_true (List.mem_filter.mp listed).2
    exact (childWellFormed_edge nodes successor wellFormed selected).2.2

/-- Process every selected routing vertex once.  The member list already
has strict topological order; no new order or route witness is chosen. -/
def steps (nodes sources : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) : List (HedgeLinearReadoutStep S) :=
  (NodeSet.members nodes).map (step nodes sources successor wellFormed noise)

theorem steps_ordered (nodes sources : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) :
    (steps nodes sources successor wellFormed noise).Pairwise
      (fun first second => first.pivot.val < second.pivot.val) :=
  List.Pairwise.map (step nodes sources successor wellFormed noise) (fun _ _ earlier => earlier)
    (NodeSet.members_pairwise_val_lt nodes)

/-- The generated explicit parent list has the exact incoming-flow parity
used by the conservation theorem, rather than an assumed equivalent signal. -/
theorem parentNodes_parity (rich : ObservedSignature.ValueRich S)
    (successor : ForestChild S) (child : Fin S.count) (sample : S.Assignment) :
    hedgeParityList rich (parentNodes successor child) sample =
      hedgeRoutingIncomingBits successor (fun parent => hedgeIsSecond rich parent (sample parent)) child := by
  unfold hedgeParityList parentNodes hedgeRoutingIncomingBits
  rw [List.foldl_filter]
  apply foldl_congr
  intro total parent
  unfold hedgeRoutingParentEntry
  by_cases selected : successor parent = some child
  · simp only [decide_eq_true selected, if_pos selected, ↓reduceIte]
  · simp only [decide_eq_false selected, if_neg selected, Bool.false_eq_true, ↓reduceIte, Bool.xor_false]

/-- Every selected vertex satisfies the additive source/incoming-flow
equation after the generated zero-bit sweep.  Its source bit is the original
assignment's bit, even if another source has an earlier route into it. -/
theorem zeroNoiseAssignment_flow (rich : ObservedSignature.ValueRich S)
    (nodes sources : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (sample : S.Assignment)
    (child : Fin S.count) (selected : nodes child = true) :
    let final := HedgeLinearReadoutPlan.zeroNoiseAssignment rich (steps nodes sources successor wellFormed noise) sample
    hedgeIsSecond rich child (final child) =
      Bool.xor (if sources child then hedgeIsSecond rich child (sample child) else false)
        (hedgeRoutingIncomingBits successor (fun parent => hedgeIsSecond rich parent (final parent)) child) := by
  have listed : step nodes sources successor wellFormed noise child ∈ steps nodes sources successor wellFormed noise :=
    List.mem_map.mpr ⟨child, (NodeSet.mem_members_iff nodes child).mpr selected, rfl⟩
  have equation := HedgeLinearReadoutPlan.zeroNoiseAssignment_local rich
    (steps nodes sources successor wellFormed noise) sample (steps_ordered nodes sources successor wellFormed noise)
    (step nodes sources successor wellFormed noise child) listed
  change hedgeIsSecond rich child
      (HedgeLinearReadoutPlan.zeroNoiseAssignment rich (steps nodes sources successor wellFormed noise) sample child) =
    Bool.xor (if sources child then hedgeIsSecond rich child (sample child) else false)
      (hedgeParityList rich (parentNodes successor child)
        (HedgeLinearReadoutPlan.zeroNoiseAssignment rich (steps nodes sources successor wellFormed noise) sample)) at equation
  rw [parentNodes_parity] at equation
  exact equation

/-- The generated final sink event pulls back to the original source
parity.  The proof is uniform in the forest size, source count, merges,
sink count, observed alphabets, and vertex-specific noise records. -/
theorem pullback_sinkParity (rich : ObservedSignature.ValueRich S)
    (nodes sources : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool nodes successor = true)
    (sourceSubset : NodeSet.Subset sources nodes)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) (sample : S.Assignment) :
    hedgeParityList rich (HedgeLinearReadoutPlan.pullbackNodes (steps nodes sources successor wellFormed noise)
      (NodeSet.members (keptSinks nodes successor))) sample =
      hedgeRootParityEvent rich sources sample := by
  let plan := steps nodes sources successor wellFormed noise
  let final := HedgeLinearReadoutPlan.zeroNoiseAssignment rich plan sample
  have flow := hedgeRoutingFlow_conservation nodes successor wellFormed
    (fun node => if sources node then hedgeIsSecond rich node (sample node) else false)
    (fun node => hedgeIsSecond rich node (final node))
    (fun child selected => zeroNoiseAssignment_flow rich nodes sources successor wellFormed noise sample child selected)
  rw [hedgeNodeXor_mask_of_subset sources nodes sourceSubset] at flow
  calc
    _ = hedgeParityList rich (NodeSet.members (keptSinks nodes successor)) final :=
      (HedgeLinearReadoutPlan.pullback_zeroNoiseAssignment rich plan
        (NodeSet.members (keptSinks nodes successor)) sample).symm
    _ = hedgeRootParityEvent rich sources sample := flow

end HedgeRoutingReadoutPlan

/-! ## Automatic positive countermodels on sink-only all-root routes -/

/-- The canonical all-root plan uses the hedge's existing finite routes,
injects every common root, and retains a separate supplied noise factor at
each routed vertex. -/
def HedgeWitness.rootReadoutPlan
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool) : List (HedgeLinearReadoutStep S) :=
  HedgeRoutingReadoutPlan.steps w.rootReadoutNodes w.roots w.rootReadoutSuccessor
    w.rootReadoutSuccessor_wellFormed noise

/-- The generated all-root plan preserves full observational equality even
when it re-enters an internal small-forest vertex.  The caller checks only
that route pivots avoid the outer-only forest; no sink or non-influence
certificate is requested.  This is the observational part of routing, not
an assertion of interventional separation for the same plan. -/
theorem HedgeWitness.carrierDefectParityModels_rootReadoutPlan_observationally_equivalent_of_small_or_outside
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (allowed : forall node, w.rootReadoutNodes node = true ->
      w.small node = true ∨ w.large node = false) :
    ObservationallyEquivalent
      ((w.largeCarrierDefectParityModel rich).withHedgeReadouts rich
        (HedgeLinearReadoutPlan.readouts rich (w.rootReadoutPlan noise)))
      ((w.smallCarrierDefectParityModel rich).withHedgeReadouts rich
        (HedgeLinearReadoutPlan.readouts rich (w.rootReadoutPlan noise))) := by
  apply w.carrierDefectParityModels_withHedgeReadouts_observationally_equivalent_of_small_or_outside rich
  intro instruction listed
  rcases List.mem_map.mp listed with ⟨linear, inPlan, same⟩
  subst instruction
  rcases List.mem_map.mp inPlan with ⟨node, member, same⟩
  subst linear
  exact allowed node ((NodeSet.mem_members_iff w.rootReadoutNodes node).mp member)

/-- Produce an original-query positive countermodel without asking for a
hand-written plan or a pullback identity.  The routing hypothesis is exactly
the initial non-influence condition of the carrier construction: every
vertex on the canonical root routes has no kept outgoing c-forest edge.

This allows arbitrarily many roots, merging routes, and multiple original
outcomes.  Positive supported biased noise may be different at every vertex.
The theorem does not remove the sink hypothesis: its interventional event
substitution is still sink-based.  The observational theorem above already
accounts for internal small-forest response, but does not prove that the
final queried parity retains the needed root signal in those cases. -/
noncomputable def HedgeWitness.positiveCounterexampleOfRootReadoutSinksWithNoise
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (sinks : forall node, w.rootReadoutNodes node = true -> w.child node = none)
    (noise : (node : Fin S.count) -> FiniteProbRecord Bool)
    (noisePositive : forall node, w.rootReadoutNodes node = true ->
      forall bit, (noise node).EventPositive (FiniteProbRecord.singletonEvent bit))
    (biased : forall node, w.rootReadoutNodes node = true -> Exists fun gap =>
      0 < gap ∧ FiniteProbRecord.eventMass (noise node).atoms (fun bit => !bit) =
        FiniteProbRecord.eventMass (noise node).atoms id + gap) :
    CounterexampleIn (GraphModelClass.positive G) q := by
  apply w.positiveCounterexampleOfReadoutPlan rich (w.rootReadoutPlan noise)
    (HedgeRoutingReadoutPlan.steps_ordered w.rootReadoutNodes w.roots w.rootReadoutSuccessor
      w.rootReadoutSuccessor_wellFormed noise)
    (nodes := NodeSet.members (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor))
  · intro instruction listed
    rcases List.mem_map.mp listed with ⟨node, member, same⟩
    subst instruction
    exact sinks node ((NodeSet.mem_members_iff w.rootReadoutNodes node).mp member)
  · intro instruction listed
    rcases List.mem_map.mp listed with ⟨node, member, same⟩
    subst instruction
    exact w.rootReadoutNodes_avoids_action node ((NodeSet.mem_members_iff w.rootReadoutNodes node).mp member)
  · intro instruction listed
    rcases List.mem_map.mp listed with ⟨node, member, same⟩
    subst instruction
    exact noisePositive node ((NodeSet.mem_members_iff w.rootReadoutNodes node).mp member)
  · intro instruction listed
    rcases List.mem_map.mp listed with ⟨node, member, same⟩
    subst instruction
    exact biased node ((NodeSet.mem_members_iff w.rootReadoutNodes node).mp member)
  · intro node member
    exact w.rootReadoutSinks_subset_outcome node
      ((NodeSet.mem_members_iff (keptSinks w.rootReadoutNodes w.rootReadoutSuccessor) node).mp member)
  · intro sample
    exact HedgeRoutingReadoutPlan.pullback_sinkParity rich w.rootReadoutNodes w.roots w.rootReadoutSuccessor
      w.rootReadoutSuccessor_wellFormed w.roots_subset_rootReadoutNodes noise sample

/-- A fixed positive biased private factor for the automatic constructor.
Stay mass two and flip mass one provide full Boolean support while retaining
a nonzero gap.  This is actual finite data, not a small-noise limit. -/
def hedgeReadoutNoise : FiniteProbRecord Bool :=
  FiniteProbRecord.biasedFlip 1 1 (by decide)

theorem hedgeReadoutNoise_positive (bit : Bool) :
    hedgeReadoutNoise.EventPositive (FiniteProbRecord.singletonEvent bit) := by
  cases bit <;> decide +kernel

theorem hedgeReadoutNoise_bias : FiniteProbRecord.eventMass hedgeReadoutNoise.atoms (fun bit => !bit) =
    FiniteProbRecord.eventMass hedgeReadoutNoise.atoms id + 1 := by decide +kernel

/-- The automatic original-query constructor with a uniform explicit
private-noise factor.  Only the geometric sink condition remains a premise;
ordering, support, bias, outcome locality, and all-root event substitution
are internal proved facts. -/
noncomputable def HedgeWitness.positiveCounterexampleOfRootReadoutSinks
    {G : ObservedGraph S} {q : JointKernelQuery S} (w : HedgeWitness G q)
    (rich : ObservedSignature.ValueRich S)
    (sinks : forall node, w.rootReadoutNodes node = true -> w.child node = none) :
    CounterexampleIn (GraphModelClass.positive G) q :=
  w.positiveCounterexampleOfRootReadoutSinksWithNoise rich sinks (fun _ => hedgeReadoutNoise)
    (fun _ _ => hedgeReadoutNoise_positive)
    (fun _ _ => ⟨1, by decide, hedgeReadoutNoise_bias⟩)

end Causality
end Thesis
