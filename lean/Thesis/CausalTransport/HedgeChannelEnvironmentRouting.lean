import Thesis.CausalTransport.HedgeChannelEnvironmentCovariance
import Thesis.CausalTransport.HedgeChannelFlowDirection

namespace Thesis
namespace Causality
namespace HedgeChannelEnvironmentInstallation

open Probability PathSpecification HedgeChannelInstallation FiniteBooleanInteraction

variable {S : ObservedSignature.{0}} {G : ObservedGraph S}

/-!
# Conditional countermodels from a freely chosen certified successor forest

The earlier matched-marginal construction fixes the original composed hedge
flow.  A combined active-path construction needs to modify that routing, so
its semantic conclusion must not depend on that particular child policy.

Here any actual action-free successor forest containing the entire Small set
can be used, provided its sinks belong to the unchanged outcome/condition
union.  The same legal signal is installed at Small and background rows:
each row reads its actual incoming kept parents and retains its own bit once.
The background selection is exactly the domain outside Small, even when a
later routing policy changes successors at a Small intersection.

An actual complete unconditioned path from any Small source supplies an odd
direction.  All outside-Small rows are even at that direction, and whole-flow
conservation proves the original-cylinder matching identity.  The outcome
mask is the actual queried sink subset, not an enlarged outcome or one
arbitrarily selected endpoint.  The general covariance constructor supplies
positive full-original-alphabet countermodels without a matched-denominator
or probability-gap premise.

This discharges a semantic family, not every irreducible conditional terminal.
The remaining active-path branch must still construct a suitable combined
signal and direction when every simple forward Small path meets a conditioner.
-/

namespace LinearSignal

/-- One common legal incoming-parent signal for the supplied map.  Edge
guards in `signal` still ignore malformed entries; no unavailable parent or
extra reserved-root input is introduced by this mask definition. -/
def ofSuccessor (successor : ForestChild S) : LinearSignal G where
  parentMask := fun child parent => decide (successor parent = some child)
  rootMask := fun _ _ => false

/-- The actual installed row is the exact local-source parity of the
supplied well-formed map.  Its own observed bit remains present once. -/
theorem ofSuccessor_rowPhase (domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (child : Fin S.count) (point : Cube G) :
    ((ofSuccessor (G := G) successor).rowPhase child).value point =
      hedgeRoutingLocalSource successor (cubeSample G point) child := by
  rw [rowPhase_value]
  have rootsZero : (List.finRange (pairRootCount G.binary)).foldl (fun total root => Bool.xor total
      (if pairRootIncident G.binary root child = true then
        if (ofSuccessor (G := G) successor).rootMask child root then cubeEnvironment G point root else false
      else false)) false = false := by
    apply foldl_unchanged
    intro total root
    simp only [ofSuccessor, Bool.false_eq_true, if_false, ite_self, Bool.xor_false]
  have parentsSame : (List.finRange S.count).foldl (fun total parent => Bool.xor total
      (if S.directed parent child = true then
        if (ofSuccessor (G := G) successor).parentMask child parent then cubeSample G point parent else false
      else false)) false = hedgeRoutingIncomingBits successor (cubeSample G point) child := by
    unfold hedgeRoutingIncomingBits hedgeRoutingParentEntry
    apply foldl_congr
    intro total parent
    by_cases next : successor parent = some child
    · have actual := (childWellFormed_edge domain successor wellFormed next).2.2
      simp only [ofSuccessor, next, decide_true, actual, if_true]
    · by_cases actual : S.directed parent child = true
      · simp only [ofSuccessor, next, decide_false, actual, if_true, Bool.false_eq_true, if_false]
      · simp only [ofSuccessor, next, actual, decide_false, Bool.false_eq_true, if_false]
  rw [rootsZero, parentsSame, Bool.xor_false]
  rfl

/-- Whole-domain conservation holds for the actual installed row phases,
not for an abstract substitute parent function. -/
theorem ofSuccessor_forestPhase (domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true) (point : Cube G) :
    ((ofSuccessor (G := G) successor).forestPhase domain).value point =
      hedgeNodeXor (keptSinks domain successor) (cubeSample G point) := by
  rw [forestPhase_value]
  have rows := foldl_congr _ _ false (NodeSet.members domain)
    (fun total child => congrArg (Bool.xor total) (ofSuccessor_rowPhase domain successor wellFormed child point))
  exact rows.trans (hedgeRoutingFlow_conservation_localSource domain successor wellFormed (cubeSample G point)).symm

/-- The interaction selection's complete ascending fold is the same phase
as the selected member-row fold.  Every selected row occurs once in both. -/
theorem selectedPhase_value_eq_forestPhase (data : LinearSignal G) (nodes : NodeSet S) (point : Cube G) :
    (selectedPhase (pairRootCount G.binary + S.count) S.count nodes data.rowPhase).value point =
      (data.forestPhase nodes).value point := by
  rw [selectedPhase_value_eq_foldl, forestPhase_value]
  unfold NodeSet.members
  rw [List.foldl_filter]
  apply foldl_congr
  intro total child
  cases nodes child <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.xor_false]

/-- A disjoint row partition uses one common installed signal.  It does
not XOR two separately installed rows at an overlapping Small vertex. -/
theorem forestPhase_union_of_disjoint (data : LinearSignal G) (left right : NodeSet S)
    (disjoint : NodeSet.Disjoint left right) (point : Cube G) :
    (data.forestPhase (NodeSet.union left right)).value point =
      Bool.xor ((data.forestPhase left).value point) ((data.forestPhase right).value point) :=
  signalPhase_union_of_disjoint left right disjoint
    (frozenParentSignal data.signal (cubeEnvironment G point)) (cubeSample G point)

end LinearSignal

/-! ## The actual original-outcome subset and exact conditioning cylinder -/

private theorem nodeXor_basis (nodes : NodeSet S) (coordinate : Fin S.count) :
    hedgeNodeXor nodes (basisAssignment S.count coordinate) = nodes coordinate := by
  have masked : hedgeNodeXor nodes (basisAssignment S.count coordinate) =
      (List.finRange S.count).foldl (fun total child => Bool.xor total
        (if nodes child then basisAssignment S.count coordinate child else false)) false := by
    unfold hedgeNodeXor NodeSet.members
    rw [List.foldl_filter]
    apply foldl_congr
    intro total child
    cases nodes child <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.xor_false]
  exact masked.trans (basisAssignment_masked_foldl S.count coordinate nodes)

private theorem nodeXor_zero (nodes : NodeSet S) : hedgeNodeXor nodes (fun _ => false) = false := by
  apply foldl_unchanged
  intro total child
  exact Bool.xor_false total

private theorem cubeMask_subset (left right : NodeSet S) (subset : NodeSet.Subset left right) :
    forall coordinate, cubeMask G left coordinate = true -> cubeMask G right coordinate = true := by
  intro coordinate selected
  unfold cubeMask FiniteProduct.BooleanBlocks.join at selected ⊢
  by_cases earlier : coordinate.val < pairRootCount G.binary
  · rw [dif_pos earlier] at selected
    cases selected
  · rw [dif_neg earlier] at selected ⊢
    exact subset _ selected

private theorem cubeMask_outcome_member {query : ConditionalKernelQuery S}
    (nodes : NodeSet S) (subset : NodeSet.Subset nodes query.outcome) :
    cubeMask G nodes ∈ outcomeMasks (pairRootCount G.binary + S.count) (cubeMask G query.outcome) := by
  apply (FiniteProduct.falseCylinderEnumeration_member_iff _ _ _).mpr
  intro coordinate omitted
  have absent : cubeMask G query.outcome coordinate = false := by
    simpa only [Bool.not_eq_true'] using omitted
  cases selected : cubeMask G nodes coordinate with
  | false => rfl
  | true =>
      have queried := cubeMask_subset nodes query.outcome subset coordinate selected
      rw [absent] at queried
      cases queried

private theorem joinCube_mem {query : ConditionalKernelQuery S} (bits : S.binary.Assignment)
    (actionFixed : forall child, query.action child = true -> bits child = false)
    (conditionFixed : forall child, query.condition child = true -> bits child = false) :
    joinCube G (fun _ => false) bits ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union query.action query.condition)) := by
  apply (FiniteProduct.BooleanBlocks.cylinder_member_iff _ _ _ _).mpr
  simp only [cubeMask, joinCube, FiniteProduct.BooleanBlocks.leftBlock_join,
    FiniteProduct.BooleanBlocks.rightBlock_join]
  constructor
  · apply (FiniteProduct.falseCylinderEnumeration_member_iff _ _ _).mpr
    intro _ impossible
    cases impossible
  · apply (FiniteProduct.falseCylinderEnumeration_member_iff _ _ _).mpr
    intro child selected
    rcases Bool.or_eq_true_iff.mp selected with acted | conditioned
    · exact actionFixed child acted
    · exact conditionFixed child conditioned

/-! ## Assemble a parity witness without fixing the original hedge policy -/

/-- A complete unconditioned Small-source path in any supplied certified
forest yields the actual finite parity witness.  All Small rows are mandatory;
the remaining selected rows are exactly the domain's outside-Small part.
No odd-phase, positive-covariance, or semantic-separation flag is supplied. -/
def ConditionalParityWitness.ofSuccessorPath {query : ConditionalKernelQuery S}
    (w : HedgeWitness G query.jointNumerator) (domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true)
    (containsSmall : NodeSet.Subset w.small domain)
    (actionFree : forall child, domain child = true -> query.action child = false)
    (sinksQueried : NodeSet.Subset (keptSinks domain successor) (NodeSet.union query.outcome query.condition))
    (source : Fin S.count) (inSmall : w.small source = true)
    (path : SuccessorPath domain successor source)
    (unconditioned : forall child, child ∈ path.nodes -> query.condition child = false) :
    ConditionalParityWitness w (LinearSignal.ofSuccessor successor) (LinearSignal.ofSuccessor successor) := by
  let data : LinearSignal G := .ofSuccessor successor
  let selected := NodeSet.diff domain w.small
  let outcomeNodes := NodeSet.inter (keptSinks domain successor) query.outcome
  let direction := joinCube G (fun _ => false) path.bits
  have listed : direction ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount G.binary + S.count)
      (cubeMask G (NodeSet.union query.action query.condition)) :=
    joinCube_mem path.bits
      (path.bits_false_of_free query.action (fun child member => actionFree child (path.inside child member)))
      (path.bits_false_of_free query.condition unconditioned)
  have unionPhase : forall point : Cube G,
      Bool.xor ((data.forestPhase w.small).value point)
        ((selectedPhase _ S.count selected data.rowPhase).value point) = (data.forestPhase domain).value point := by
    intro point
    rw [LinearSignal.selectedPhase_value_eq_forestPhase, ← LinearSignal.forestPhase_union_of_disjoint data w.small selected
      (NodeSet.disjoint_diff domain w.small), NodeSet.union_diff_eq containsSmall]
  have basis_matches : forall coordinate, cubeMask G (NodeSet.union query.action query.condition) coordinate = false ->
      ((data.forestPhase w.small).xor (maskPhase _ (cubeMask G outcomeNodes))).value (basisAssignment _ coordinate) =
        (selectedPhase _ S.count selected data.rowPhase).value (basisAssignment _ coordinate) := by
    intro coordinate free
    have maskEq : (maskPhase _ (cubeMask G outcomeNodes)).value (basisAssignment _ coordinate) =
        (data.forestPhase domain).value (basisAssignment _ coordinate) := by
      rw [maskPhase_basis, LinearSignal.ofSuccessor_forestPhase domain successor wellFormed]
      by_cases earlier : coordinate.val < pairRootCount G.binary
      · let root : Fin (pairRootCount G.binary) := ⟨coordinate.val, earlier⟩
        have embedded : root.castAdd S.count = coordinate := Fin.ext rfl
        rw [← embedded]
        change FiniteProduct.BooleanBlocks.leftBlock _ _ (cubeMask G outcomeNodes) root = _
        rw [cubeMask, FiniteProduct.BooleanBlocks.leftBlock_join, cubeSample,
          rightBlock_basis_left, nodeXor_zero]
      · let child : Fin S.count := ⟨coordinate.val - pairRootCount G.binary, by omega⟩
        have embedded : Fin.natAdd (pairRootCount G.binary) child = coordinate := by
          apply Fin.ext
          dsimp only [child, Fin.natAdd]
          omega
        have freeChild : NodeSet.union query.action query.condition child = false := by
          rw [← embedded] at free
          change FiniteProduct.BooleanBlocks.rightBlock _ _ (cubeMask G _) child = false at free
          simpa only [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join] using free
        have conditionFree : query.condition child = false := by
          cases conditioned : query.condition child with
          | false => rfl
          | true =>
              have impossible : (query.action child || true) = false := by
                simpa only [NodeSet.union, conditioned] using freeChild
              simp only [Bool.or_true] at impossible
              cases impossible
        rw [← embedded]
        change FiniteProduct.BooleanBlocks.rightBlock _ _ (cubeMask G outcomeNodes) child = _
        rw [cubeMask, FiniteProduct.BooleanBlocks.rightBlock_join, cubeSample, rightBlock_basis_right, nodeXor_basis]
        cases sink : keptSinks domain successor child with
        | false => simp only [outcomeNodes, NodeSet.inter, sink, Bool.false_and]
        | true =>
            have queried := sinksQueried child sink
            have outcomeSelected : query.outcome child = true := by
              simpa only [NodeSet.union, conditionFree, Bool.or_false] using queried
            simp only [outcomeNodes, NodeSet.inter, sink, outcomeSelected, Bool.and_self]
    change Bool.xor ((data.forestPhase w.small).value _) ((maskPhase _ (cubeMask G outcomeNodes)).value _) = _
    rw [maskEq, ← unionPhase]
    generalize (data.forestPhase w.small).value (basisAssignment _ coordinate) = smallBit
    generalize (selectedPhase _ S.count selected data.rowPhase).value (basisAssignment _ coordinate) = backgroundBit
    cases smallBit <;> cases backgroundBit <;> rfl
  have matching := (HomogeneousPhase.agree_on_falseCylinder_iff_basis
    ((data.forestPhase w.small).xor (maskPhase _ (cubeMask G outcomeNodes)))
    (selectedPhase _ S.count selected data.rowPhase) (cubeMask G (NodeSet.union query.action query.condition))).mpr basis_matches
  have rowDirection : forall child, (data.rowPhase child).value direction = decide (child = source) := by
    intro child
    rw [LinearSignal.ofSuccessor_rowPhase domain successor wellFormed, cubeSample_joinCube, path.bits_localSource]
  have even : forall child, selected child = true -> (data.rowPhase child).value direction = false := by
    intro child chosen
    rw [rowDirection]
    apply decide_eq_false
    intro same
    subst child
    have notSmall : Bool.not (w.small source) = true := (Bool.and_eq_true_iff.mp chosen).2
    rw [inSmall] at notSmall
    cases notSmall
  have smallOdd : (data.forestPhase w.small).value direction = true := by
    rw [LinearSignal.forestPhase_value]
    have rows := foldl_congr _ _ false (NodeSet.members w.small)
      (fun total child => congrArg (Bool.xor total) (rowDirection child))
    exact rows.trans (foldl_xor_indicator_of_mem_nodup (NodeSet.members w.small) source
      ((NodeSet.mem_members_iff w.small source).mpr inSmall) (NodeSet.nodup_members w.small))
  have outcomeOdd : (maskPhase _ (cubeMask G outcomeNodes)).value direction = true := by
    have matched := matching direction listed
    change Bool.xor ((data.forestPhase w.small).value direction)
      ((maskPhase _ (cubeMask G outcomeNodes)).value direction) = _ at matched
    rw [smallOdd, selectedPhase_value_eq_false_of_even _ _ selected data.rowPhase direction even] at matched
    cases bit : (maskPhase _ (cubeMask G outcomeNodes)).value direction with
    | false => rw [bit] at matched; cases matched
    | true => rfl
  exact {
    outcomeMask := cubeMask G outcomeNodes
    outcomeMask_member := cubeMask_outcome_member outcomeNodes (NodeSet.inter_subset_right _ _)
    direction := direction
    direction_member := listed
    small_odd := smallOdd
    outcome_odd := outcomeOdd
    selected := selected
    selected_outside_small := by
      intro child chosen
      simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp chosen).2
    selected_avoids_action := fun child chosen => actionFree child (Bool.and_eq_true_iff.mp chosen).1
    selected_even := even
    matching := matching
  }

/-- Positive full-original-alphabet countermodels for the unchanged query,
from the same freely chosen flow and actual whole unconditioned path.
The complete Small/background phases, both evidence masses, and the final
original-label lift are supplied by the proved covariance construction. -/
noncomputable def conditionalCounterexampleOfSuccessorPath {query : ConditionalKernelQuery S}
    (w : HedgeWitness G query.jointNumerator) (rich : ObservedSignature.ValueRich S)
    (domain : NodeSet S) (successor : ForestChild S)
    (wellFormed : childWellFormedBool domain successor = true)
    (containsSmall : NodeSet.Subset w.small domain)
    (actionFree : forall child, domain child = true -> query.action child = false)
    (sinksQueried : NodeSet.Subset (keptSinks domain successor) (NodeSet.union query.outcome query.condition))
    (source : Fin S.count) (inSmall : w.small source = true)
    (path : SuccessorPath domain successor source)
    (unconditioned : forall child, child ∈ path.nodes -> query.condition child = false) :
    ConditionalCounterexampleIn (GraphModelClass.positive G) query :=
  conditionalCounterexampleOfParity w rich (.ofSuccessor successor) (.ofSuccessor successor)
    (ConditionalParityWitness.ofSuccessorPath w domain successor wellFormed containsSmall actionFree sinksQueried
      source inSmall path unconditioned)

end HedgeChannelEnvironmentInstallation
end Causality
end Thesis
