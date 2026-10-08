import Thesis.CausalTransport.HedgeChannelInstallation
import Thesis.Probability.FiniteSupportedSum

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Canonical surviving choices in the installed hedge likelihood

The actual row expansion contains every permitted channel interaction.
Connected-channel integration proves that a nonzero term must select a main
channel on its entire forest.  A row has only one slot, and all large main
channels share the computed common root, so no two can survive together.
Singleton backgrounds can coexist, but only at their own original rows.

Here these facts classify the complete choices, rather than merely asserting
that one particular partial term cancels.  Reading the row choice at the
common root determines whether the term is background-only or has one full
main channel.  Its remaining background mask is computed directly from the
choice.  No witness is selected from a semantic nonzero proposition to build
a model: all existential eliminations in the classification remain in Prop.

Masks are restricted to the unconsumed rows.  Coordinates already occupied
by a full main channel are fixed false, avoiding duplicate descriptions of
the same surviving choice.  The classification is on the original actual
pair-root prior and the installed local row lists.  It does not assume an
observational equality or an original-outcome gap.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## Explicit canonical choices and their masks -/

/-- Original vertices not consumed by a given forest. -/
def outside (nodes : NodeSet S) : NodeSet S := NodeSet.diff NodeSet.full nodes

/-- Choose each singleton background exactly where the mask asks for it.
Later list membership requires the mask to avoid the small forest. -/
def backgroundChoice (w : HedgeWitness G q) (mask : NodeSet S) :
    Fin S.count -> Option (Fin (channelCount w)) :=
  fun child => if mask child then some (backgroundChannel w child) else none

/-- Fully choose one main channel on its forest and backgrounds only off
that forest.  Restricting the mask off the forest gives a unique description. -/
def fullChoice (w : HedgeWitness G q) (nodes : NodeSet S) (channel : Fin (channelCount w))
    (mask : NodeSet S) : Fin S.count -> Option (Fin (channelCount w)) :=
  fun child => if nodes child then some channel else backgroundChoice w mask child

/-- Data-level extraction of the background mask from an actual choice.
Equality is between explicit finite indices, not arbitrary propositions. -/
def backgroundMask (w : HedgeWitness G q) (choice : Fin S.count -> Option (Fin (channelCount w))) : NodeSet S :=
  fun child => decide (choice child = some (backgroundChannel w child))

/-- Forget mask bits already consumed by the main forest.  Those bits must
not create redundant entries in the canonical survivor enumeration. -/
def remainingBackgroundMask (w : HedgeWitness G q) (nodes : NodeSet S)
    (choice : Fin S.count -> Option (Fin (channelCount w))) : NodeSet S :=
  NodeSet.diff (backgroundMask w choice) nodes

theorem remainingBackgroundMask_subset (w : HedgeWitness G q) (nodes : NodeSet S)
    (choice : Fin S.count -> Option (Fin (channelCount w))) :
    NodeSet.Subset (remainingBackgroundMask w nodes choice) (outside nodes) := by
  intro child selected
  have absent := (Bool.and_eq_true_iff.mp selected).2
  exact Bool.and_eq_true_iff.mpr ⟨rfl, absent⟩

private theorem background_support (w : HedgeWitness G q) (node child : Fin S.count)
    (selected : backgroundNodes w node child = true) : child = node ∧ w.small child = false := by
  cases inside : w.small node with
  | true => simp only [backgroundNodes, inside, if_true, NodeSet.empty] at selected; cases selected
  | false =>
      have same := (NodeSet.singleton_eq_true_iff node child).mp (by
        simpa only [backgroundNodes, inside, Bool.false_eq_true, if_false] using selected)
      exact ⟨same, same ▸ inside⟩

private theorem outside_false (nodes : NodeSet S) (node : Fin S.count)
    (selected : outside nodes node = true) : nodes node = false := by
  unfold outside NodeSet.diff NodeSet.full at selected
  have absent := (Bool.and_eq_true_iff.mp selected).2
  cases present : nodes node with
  | false => rfl
  | true => rw [present] at absent; cases absent

private theorem backgroundChoice_of_none (w : HedgeWitness G q)
    (choice : Fin S.count -> Option (Fin (channelCount w))) (child : Fin S.count)
    (picked : choice child = none) : backgroundChoice w (backgroundMask w choice) child = none := by
  simp only [backgroundChoice, backgroundMask, picked, reduceCtorEq, decide_false, Bool.false_eq_true, if_false]

private theorem backgroundChoice_of_pick (w : HedgeWitness G q)
    (choice : Fin S.count -> Option (Fin (channelCount w))) (child : Fin S.count)
    (picked : choice child = some (backgroundChannel w child)) :
    backgroundChoice w (backgroundMask w choice) child = choice child := by
  simp only [backgroundChoice, backgroundMask, picked, decide_true, if_true]

/-! ## What can a genuine local row choose? -/

private theorem left_support (w : HedgeWitness G q)
    (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (leftTables w child).expansionChoicesUnder none))
    (child : Fin S.count) (channel : Fin (channelCount w)) (picked : choice child = some channel) :
    leftNodes w channel child = true :=
  HedgeChannelTable.selectedNodes_subset_of_mem (leftTables w) (leftNodes w)
    (HedgeChannelCoefficients.tables_channel_allowed _ _ _ _ _) (fun _ => none) choice member channel child
    (decide_eq_true picked)

private theorem right_support (w : HedgeWitness G q)
    (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (rightTables w child).expansionChoicesUnder none))
    (child : Fin S.count) (channel : Fin (channelCount w)) (picked : choice child = some channel) :
    rightNodes w channel child = true :=
  HedgeChannelTable.selectedNodes_subset_of_mem (rightTables w) (rightNodes w)
    (HedgeChannelCoefficients.tables_channel_allowed _ _ _ _ _) (fun _ => none) choice member channel child
    (decide_eq_true picked)

/-- Inactive slots are impossible, and a background label must name this
row itself.  The support facts come from actual local-list membership. -/
theorem left_row_cases (w : HedgeWitness G q) (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (leftTables w child).expansionChoicesUnder none)) (child : Fin S.count) :
    choice child = none ∨
      (Exists fun index : Fin (masks (outer w)).length =>
        w.large child = true ∧ choice child = some (largeChannel w index)) ∨
      (w.small child = false ∧ choice child = some (backgroundChannel w child)) := by
  cases picked : choice child with
  | none => exact Or.inl rfl
  | some channel =>
      have support := left_support w choice member child channel picked
      have reconstructed := channelOfRole_role w channel
      cases tag : role w channel with
      | large index =>
          rw [leftNodes, tag] at support
          rw [tag] at reconstructed
          exact Or.inr (Or.inl ⟨index, support, congrArg some reconstructed.symm⟩)
      | small =>
          rw [leftNodes, tag] at support
          cases support
      | background node =>
          rw [leftNodes, tag] at support
          have data := background_support w node child support
          rw [tag] at reconstructed
          have same : backgroundChannel w child = channel := data.1 ▸ reconstructed
          exact Or.inr (Or.inr ⟨data.2, congrArg some same.symm⟩)

theorem right_row_cases (w : HedgeWitness G q) (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (rightTables w child).expansionChoicesUnder none)) (child : Fin S.count) :
    choice child = none ∨ (w.small child = true ∧ choice child = some (smallChannel w)) ∨
      (w.small child = false ∧ choice child = some (backgroundChannel w child)) := by
  cases picked : choice child with
  | none => exact Or.inl rfl
  | some channel =>
      have support := right_support w choice member child channel picked
      have reconstructed := channelOfRole_role w channel
      cases tag : role w channel with
      | large _ => rw [rightNodes, tag] at support; cases support
      | small =>
          rw [rightNodes, tag] at support
          rw [tag] at reconstructed
          exact Or.inr (Or.inl ⟨support, congrArg some reconstructed.symm⟩)
      | background node =>
          rw [rightNodes, tag] at support
          have data := background_support w node child support
          rw [tag] at reconstructed
          have same : backgroundChannel w child = channel := data.1 ▸ reconstructed
          exact Or.inr (Or.inr ⟨data.2, congrArg some same.symm⟩)

private theorem left_backgroundMask_subset (w : HedgeWitness G q)
    (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (leftTables w child).expansionChoicesUnder none)) :
    NodeSet.Subset (backgroundMask w choice) (outside w.small) := by
  intro child selected
  have picked : choice child = some (backgroundChannel w child) := of_decide_eq_true selected
  have support := left_support w choice member child (backgroundChannel w child) picked
  rw [leftNodes, role_backgroundChannel] at support
  have data := background_support w child child support
  simp only [outside, NodeSet.diff, NodeSet.full, data.2, Bool.not_false, Bool.and_self]

private theorem right_backgroundMask_subset (w : HedgeWitness G q)
    (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (rightTables w child).expansionChoicesUnder none)) :
    NodeSet.Subset (backgroundMask w choice) (outside w.small) := by
  intro child selected
  have picked : choice child = some (backgroundChannel w child) := of_decide_eq_true selected
  have support := right_support w choice member child (backgroundChannel w child) picked
  rw [rightNodes, role_backgroundChannel] at support
  have data := background_support w child child support
  simp only [outside, NodeSet.diff, NodeSet.full, data.2, Bool.not_false, Bool.and_self]

/-! ## Classifying nonzero actual monomial integrals -/

/-- A left nonzero term is either entirely background choices, or one
fully selected large channel with backgrounds only outside the large forest.
The conclusion retains all legal background interactions and provides an
explicit computed mask for each description. -/
theorem left_nonzero_choice (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (leftTables w child).expansionChoicesUnder none))
    (nonzero : (PairRootChannels.prior G.binary (channelCount w)).signedMass
      (HedgeChannelTable.choiceMonomial G (channelCount w) (leftTables w)
        (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample choice) ≠ 0) :
    (choice = backgroundChoice w (backgroundMask w choice) ∧
      NodeSet.Subset (backgroundMask w choice) (outside w.small)) ∨
    (Exists fun index : Fin (masks (outer w)).length =>
      choice = fullChoice w w.large (largeChannel w index) (remainingBackgroundMask w w.large choice) ∧
        NodeSet.Subset (remainingBackgroundMask w w.large choice) (outside w.large)) := by
  have full : forall index row, choice row = some (largeChannel w index) ->
      HedgeChannelTable.selectedNodes choice (largeChannel w index) = w.large := by
    intro index row picked
    have result := HedgeChannelTable.choiceMonomial_nonzero_full G (channelCount w) (leftTables w)
      (leftNodes w) (leftParentSignal w rich smallSignal backgroundSignal)
      (HedgeChannelCoefficients.tables_channel_allowed _ _ _ _ _)
      (fun _ => none) sample choice member nonzero (largeChannel w index)
      (by rw [leftNodes_largeChannel]; exact large_component w) row picked
    exact result.trans (leftNodes_largeChannel w index)
  rcases left_row_cases w choice member w.actionRoot with noneAtRoot | mainAtRoot | backgroundAtRoot
  · refine Or.inl ⟨?_, left_backgroundMask_subset w choice member⟩
    funext child
    rcases left_row_cases w choice member child with absent | ⟨index, _inside, picked⟩ | ⟨_outside, picked⟩
    · exact absent.trans (backgroundChoice_of_none w choice child absent).symm
    · have rootSelected : HedgeChannelTable.selectedNodes choice (largeChannel w index) w.actionRoot = true := by
        rw [full index child picked]
        exact w.actionRoot_in_large
      have rootPicked : choice w.actionRoot = some (largeChannel w index) := of_decide_eq_true rootSelected
      rw [noneAtRoot] at rootPicked
      cases rootPicked
    · exact (backgroundChoice_of_pick w choice child picked).symm
  · rcases mainAtRoot with ⟨index, _inside, picked⟩
    refine Or.inr ⟨index, ?_, remainingBackgroundMask_subset w w.large choice⟩
    funext child
    cases inside : w.large child with
    | true =>
        have selectedHere : HedgeChannelTable.selectedNodes choice (largeChannel w index) child = true := by
          rw [full index w.actionRoot picked]
          exact inside
        have choiceHere : choice child = some (largeChannel w index) := of_decide_eq_true selectedHere
        simpa only [fullChoice, inside, if_true] using choiceHere
    | false =>
        have unchanged : remainingBackgroundMask w w.large choice child = backgroundMask w choice child := by
          simp only [remainingBackgroundMask, NodeSet.diff, inside, Bool.not_false, Bool.and_true]
        simp only [fullChoice, inside, Bool.false_eq_true, if_false, backgroundChoice, unchanged]
        rcases left_row_cases w choice member child with absent | ⟨other, selectedHere, _otherPick⟩ | ⟨_outside, chosen⟩
        · simp only [backgroundMask, absent, reduceCtorEq, decide_false, Bool.false_eq_true, if_false]
        · rw [inside] at selectedHere
          cases selectedHere
        · simp only [backgroundMask, chosen, decide_true, if_true]
  · rw [w.actionRoot_in_small] at backgroundAtRoot
    cases backgroundAtRoot.1

/-- On the right, the same complete classification leaves either only
backgrounds or the full small channel.  The masks in both cases avoid the
small forest, and the proof uses the actual small connected component. -/
theorem right_nonzero_choice (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal S)
    (sample : S.binary.Assignment) (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (rightTables w child).expansionChoicesUnder none))
    (nonzero : (PairRootChannels.prior G.binary (channelCount w)).signedMass
      (HedgeChannelTable.choiceMonomial G (channelCount w) (rightTables w)
        (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample choice) ≠ 0) :
    (choice = backgroundChoice w (backgroundMask w choice) ∧
      NodeSet.Subset (backgroundMask w choice) (outside w.small)) ∨
    (choice = fullChoice w w.small (smallChannel w) (remainingBackgroundMask w w.small choice) ∧
      NodeSet.Subset (remainingBackgroundMask w w.small choice) (outside w.small)) := by
  have full : forall row, choice row = some (smallChannel w) ->
      HedgeChannelTable.selectedNodes choice (smallChannel w) = w.small := by
    intro row picked
    have result := HedgeChannelTable.choiceMonomial_nonzero_full G (channelCount w) (rightTables w)
      (rightNodes w) (rightParentSignal w smallSignal backgroundSignal)
      (HedgeChannelCoefficients.tables_channel_allowed _ _ _ _ _)
      (fun _ => none) sample choice member nonzero (smallChannel w)
      (by rw [rightNodes_smallChannel]; exact small_component w) row picked
    exact result.trans (rightNodes_smallChannel w)
  rcases right_row_cases w choice member w.actionRoot with noneAtRoot | mainAtRoot | backgroundAtRoot
  · refine Or.inl ⟨?_, right_backgroundMask_subset w choice member⟩
    funext child
    rcases right_row_cases w choice member child with absent | ⟨_inside, picked⟩ | ⟨_outside, picked⟩
    · exact absent.trans (backgroundChoice_of_none w choice child absent).symm
    · have rootSelected : HedgeChannelTable.selectedNodes choice (smallChannel w) w.actionRoot = true := by
        rw [full child picked]
        exact w.actionRoot_in_small
      have rootPicked : choice w.actionRoot = some (smallChannel w) := of_decide_eq_true rootSelected
      rw [noneAtRoot] at rootPicked
      cases rootPicked
    · exact (backgroundChoice_of_pick w choice child picked).symm
  · refine Or.inr ⟨?_, remainingBackgroundMask_subset w w.small choice⟩
    funext child
    cases inside : w.small child with
    | true =>
        have selectedHere : HedgeChannelTable.selectedNodes choice (smallChannel w) child = true := by
          rw [full w.actionRoot mainAtRoot.2]
          exact inside
        have choiceHere : choice child = some (smallChannel w) := of_decide_eq_true selectedHere
        simpa only [fullChoice, inside, if_true] using choiceHere
    | false =>
        have unchanged : remainingBackgroundMask w w.small choice child = backgroundMask w choice child := by
          simp only [remainingBackgroundMask, NodeSet.diff, inside, Bool.not_false, Bool.and_true]
        simp only [fullChoice, inside, Bool.false_eq_true, if_false, backgroundChoice, unchanged]
        rcases right_row_cases w choice member child with absent | ⟨selectedHere, _otherPick⟩ | ⟨_outside, chosen⟩
        · simp only [backgroundMask, absent, reduceCtorEq, decide_false, Bool.false_eq_true, if_false]
        · rw [inside] at selectedHere
          cases selectedHere
        · simp only [backgroundMask, chosen, decide_true, if_true]
  · rw [w.actionRoot_in_small] at backgroundAtRoot
    cases backgroundAtRoot.1

/-! ## Complete repetition-free canonical survivor lists -/

private instance choiceDecidableEq (w : HedgeWitness G q) :
    DecidableEq (Fin S.count -> Option (Fin (channelCount w))) :=
  FiniteProduct.assignmentDecidableEq S.count (fun _ => Option (Fin (channelCount w))) (fun _ => inferInstance)

/-- All background-only descriptions, with one mask per actual choice. -/
def commonChoices (w : HedgeWitness G q) : List (Fin S.count -> Option (Fin (channelCount w))) :=
  (masks (outside w.small)).map (backgroundChoice w)

/-- One complete large channel and every legal background mask outside it.
The two levels of enumeration retain each channel and each mask exactly once. -/
def leftFullChoices (w : HedgeWitness G q) : List (Fin S.count -> Option (Fin (channelCount w))) :=
  (List.finRange (masks (outer w)).length).flatMap (fun index =>
    (masks (outside w.large)).map (fullChoice w w.large (largeChannel w index)))

def rightFullChoices (w : HedgeWitness G q) : List (Fin S.count -> Option (Fin (channelCount w))) :=
  (masks (outside w.small)).map (fullChoice w w.small (smallChannel w))

def leftSurvivors (w : HedgeWitness G q) := commonChoices w ++ leftFullChoices w
def rightSurvivors (w : HedgeWitness G q) := commonChoices w ++ rightFullChoices w

private theorem background_bit_injective (w : HedgeWitness G q) (left right : NodeSet S) (child : Fin S.count)
    (same : backgroundChoice w left child = backgroundChoice w right child) : left child = right child := by
  cases leftBit : left child <;> cases rightBit : right child <;>
    simp only [backgroundChoice, leftBit, rightBit, Bool.false_eq_true, if_false, if_true] at same ⊢
  · cases same
  · cases same

private theorem backgroundChoice_injective (w : HedgeWitness G q) : Function.Injective (backgroundChoice w) := by
  intro left right same
  exact funext (fun child => background_bit_injective w left right child (congrFun same child))

private theorem mask_false_inside (nodes mask : NodeSet S) (subset : NodeSet.Subset mask (outside nodes))
    (child : Fin S.count) (inside : nodes child = true) : mask child = false := by
  cases selected : mask child with
  | false => rfl
  | true =>
      have absent := outside_false nodes child (subset child selected)
      rw [inside] at absent
      cases absent

private theorem fullChoice_mask_injective (w : HedgeWitness G q) (nodes : NodeSet S)
    (channel : Fin (channelCount w)) (left right : NodeSet S)
    (leftSubset : NodeSet.Subset left (outside nodes)) (rightSubset : NodeSet.Subset right (outside nodes))
    (same : fullChoice w nodes channel left = fullChoice w nodes channel right) : left = right := by
  funext child
  cases inside : nodes child with
  | true =>
      exact (mask_false_inside nodes left leftSubset child inside).trans
        (mask_false_inside nodes right rightSubset child inside).symm
  | false =>
      have localSame := congrFun same child
      simp only [fullChoice, inside, Bool.false_eq_true, if_false] at localSame
      exact background_bit_injective w left right child localSame

private theorem fullChoices_mask_nodup (w : HedgeWitness G q) (nodes : NodeSet S) (channel : Fin (channelCount w)) :
    ((masks (outside nodes)).map (fullChoice w nodes channel)).Nodup :=
  ConstructivePermutation.nodup_map_of_injective_on _ _
    (fun left leftMember right rightMember same => fullChoice_mask_injective w nodes channel left right
      ((masks_member_iff _ _).mp leftMember) ((masks_member_iff _ _).mp rightMember) same)
    (masks_nodup _)

private theorem commonChoices_root_none (w : HedgeWitness G q)
    (choice : Fin S.count -> Option (Fin (channelCount w))) (member : choice ∈ commonChoices w) :
    choice w.actionRoot = none := by
  rcases List.mem_map.mp member with ⟨mask, maskMember, same⟩
  rw [← same]
  have absent := mask_false_inside w.small mask ((masks_member_iff _ _).mp maskMember)
    w.actionRoot w.actionRoot_in_small
  simp only [backgroundChoice, absent, Bool.false_eq_true, if_false]

private theorem leftFullChoices_root_some (w : HedgeWitness G q)
    (choice : Fin S.count -> Option (Fin (channelCount w))) (member : choice ∈ leftFullChoices w) :
    Exists fun index : Fin (masks (outer w)).length => choice w.actionRoot = some (largeChannel w index) := by
  rcases List.mem_flatMap.mp member with ⟨index, _indexMember, mapped⟩
  rcases List.mem_map.mp mapped with ⟨mask, _maskMember, same⟩
  refine ⟨index, ?_⟩
  rw [← same]
  simp only [fullChoice, w.actionRoot_in_large, if_true]

private theorem rightFullChoices_root_some (w : HedgeWitness G q)
    (choice : Fin S.count -> Option (Fin (channelCount w))) (member : choice ∈ rightFullChoices w) :
    choice w.actionRoot = some (smallChannel w) := by
  rcases List.mem_map.mp member with ⟨mask, _maskMember, same⟩
  rw [← same]
  simp only [fullChoice, w.actionRoot_in_small, if_true]

private theorem commonChoices_nodup (w : HedgeWitness G q) : (commonChoices w).Nodup :=
  ConstructivePermutation.nodup_map_of_injective_on _ _
    (fun _ _ _ _ same => backgroundChoice_injective w same) (masks_nodup _)

private theorem leftFullChoices_nodup (w : HedgeWitness G q) : (leftFullChoices w).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro index _member
    exact fullChoices_mask_nodup w w.large (largeChannel w index)
  · apply (nodup_finRange (masks (outer w)).length).imp
    intro first second different left leftMember right rightMember same
    rcases List.mem_map.mp leftMember with ⟨leftMask, _leftMaskMember, leftEq⟩
    rcases List.mem_map.mp rightMember with ⟨rightMask, _rightMaskMember, rightEq⟩
    have rootEq := congrFun (leftEq.trans (same.trans rightEq.symm)) w.actionRoot
    simp only [fullChoice, w.actionRoot_in_large, if_true, Option.some.injEq] at rootEq
    exact different (Fin.ext (congrArg (fun channel : Fin (channelCount w) => channel.val) rootEq))

/-- Every left canonical term is counted once.  The common root separates
the background-only block from all complete large-channel blocks. -/
theorem leftSurvivors_nodup (w : HedgeWitness G q) : (leftSurvivors w).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨commonChoices_nodup w, leftFullChoices_nodup w, ?_⟩
  intro left leftMember right rightMember same
  have absent := commonChoices_root_none w left leftMember
  rcases leftFullChoices_root_some w right rightMember with ⟨index, present⟩
  rw [← same, absent] at present
  cases present

theorem rightSurvivors_nodup (w : HedgeWitness G q) : (rightSurvivors w).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨commonChoices_nodup w, fullChoices_mask_nodup w w.small (smallChannel w), ?_⟩
  intro left leftMember right rightMember same
  have absent := commonChoices_root_none w left leftMember
  have present := rightFullChoices_root_some w right rightMember
  rw [← same, absent] at present
  cases present

private theorem local_channel_member (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat)
    (child : Fin S.count) (channel : Fin channels) (selected : nodes channel child = true) :
    channel ∈ (HedgeChannelCoefficients.tables channels bound nodes anchors deficits child).channels :=
  List.mem_filter.mpr ⟨List.mem_finRange channel, selected⟩

private theorem background_channel_member (w : HedgeWitness G q)
    (nodes : Fin (channelCount w) -> NodeSet S)
    (same : forall child, nodes (backgroundChannel w child) = backgroundNodes w child)
    (anchors : Fin (channelCount w) -> Option (Fin S.count)) (deficits : Fin (channelCount w) -> Nat)
    (child : Fin S.count) (outsideSmall : w.small child = false) :
    backgroundChannel w child ∈ (HedgeChannelCoefficients.tables (channelCount w) S.count nodes anchors deficits child).channels := by
  apply local_channel_member
  rw [same, backgroundNodes, outsideSmall]
  exact (NodeSet.singleton_eq_true_iff child child).mpr rfl

private theorem backgroundChoice_member (w : HedgeWitness G q)
    (nodes : Fin (channelCount w) -> NodeSet S)
    (same : forall child, nodes (backgroundChannel w child) = backgroundNodes w child)
    (anchors : Fin (channelCount w) -> Option (Fin S.count)) (deficits : Fin (channelCount w) -> Nat)
    (mask : NodeSet S) (subset : NodeSet.Subset mask (outside w.small)) :
    backgroundChoice w mask ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (HedgeChannelCoefficients.tables (channelCount w) S.count nodes anchors deficits child).expansionChoicesUnder none) := by
  apply FiniteProduct.enumeration_mem_of_coordinate_mem
  intro child
  cases selected : mask child with
  | false =>
      simp only [backgroundChoice, selected, Bool.false_eq_true, if_false]
      exact List.mem_cons_self
  | true =>
      simp only [backgroundChoice, selected, if_true]
      apply List.mem_cons_of_mem
      exact List.mem_map_of_mem (background_channel_member w nodes same anchors deficits child
        (outside_false w.small child (subset child selected)))

private theorem fullChoice_member (w : HedgeWitness G q)
    (nodes : Fin (channelCount w) -> NodeSet S)
    (same : forall child, nodes (backgroundChannel w child) = backgroundNodes w child)
    (anchors : Fin (channelCount w) -> Option (Fin S.count)) (deficits : Fin (channelCount w) -> Nat)
    (forest : NodeSet S) (containsSmall : NodeSet.Subset w.small forest)
    (channel : Fin (channelCount w)) (support : nodes channel = forest)
    (mask : NodeSet S) :
    fullChoice w forest channel mask ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (HedgeChannelCoefficients.tables (channelCount w) S.count nodes anchors deficits child).expansionChoicesUnder none) := by
  apply FiniteProduct.enumeration_mem_of_coordinate_mem
  intro child
  cases inside : forest child with
  | true =>
      simp only [fullChoice, inside, if_true]
      apply List.mem_cons_of_mem
      exact List.mem_map_of_mem (local_channel_member _ _ _ _ _ child channel (support.symm ▸ inside))
  | false =>
      simp only [fullChoice, inside, Bool.false_eq_true, if_false, backgroundChoice]
      cases selected : mask child with
      | false => simp only [Bool.false_eq_true, if_false]; exact List.mem_cons_self
      | true =>
          simp only [if_true]
          have outsideSmall : w.small child = false := by
            cases inSmall : w.small child with
            | false => rfl
            | true => have inForest := containsSmall child inSmall; rw [inside] at inForest; cases inForest
          apply List.mem_cons_of_mem
          exact List.mem_map_of_mem (background_channel_member w nodes same anchors deficits child outsideSmall)

/-- Canonical terms really occur in the complete factual local-choice
product.  Neither completeness nor support is assumed for an external list. -/
theorem leftSurvivors_member (w : HedgeWitness G q) (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ leftSurvivors w) :
    choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (leftTables w child).expansionChoicesUnder none) := by
  have backgrounds : forall child, leftNodes w (backgroundChannel w child) = backgroundNodes w child := by
    intro child
    rw [leftNodes, role_backgroundChannel]
  rcases List.mem_append.mp member with common | main
  · rcases List.mem_map.mp common with ⟨mask, maskMember, same⟩
    rw [← same]
    exact backgroundChoice_member w _ backgrounds _ _ mask ((masks_member_iff _ _).mp maskMember)
  · rcases List.mem_flatMap.mp main with ⟨index, _indexMember, mapped⟩
    rcases List.mem_map.mp mapped with ⟨mask, _maskMember, same⟩
    rw [← same]
    exact fullChoice_member w _ backgrounds _ _ w.large w.small_subset_large (largeChannel w index)
      (leftNodes_largeChannel w index) mask

theorem rightSurvivors_member (w : HedgeWitness G q) (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ rightSurvivors w) :
    choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (rightTables w child).expansionChoicesUnder none) := by
  have backgrounds : forall child, rightNodes w (backgroundChannel w child) = backgroundNodes w child := by
    intro child
    rw [rightNodes, role_backgroundChannel]
  rcases List.mem_append.mp member with common | main
  · rcases List.mem_map.mp common with ⟨mask, maskMember, same⟩
    rw [← same]
    exact backgroundChoice_member w _ backgrounds _ _ mask ((masks_member_iff _ _).mp maskMember)
  · rcases List.mem_map.mp main with ⟨mask, _maskMember, same⟩
    rw [← same]
    exact fullChoice_member w _ backgrounds _ _ w.small (fun _ inside => inside) (smallChannel w)
      (rightNodes_smallChannel w) mask

/-! ## Exact reduction of the complete actual likelihood -/

private theorem coefficientChoices_nodup (channels bound : Nat) (nodes : Fin channels -> NodeSet S)
    (anchors : Fin channels -> Option (Fin S.count)) (deficits : Fin channels -> Nat) (child : Fin S.count) :
    ((HedgeChannelCoefficients.tables channels bound nodes anchors deficits child).expansionChoicesUnder none).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨channel, _channelMember, same⟩
    cases same
  · exact ConstructivePermutation.nodup_map_of_injective_on some _
      (fun _ _ _ _ same => Option.some.inj same)
      (List.Pairwise.filter _ (nodup_finRange channels))

/-- The integral of one complete row choice against the actual root-major
prior.  These are the original monomial integrals, not replacement terms
whose coefficient or phase has been assumed. -/
def leftTermIntegral (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin (channelCount w))) : Int :=
  (PairRootChannels.prior G.binary (channelCount w)).signedMass
    (HedgeChannelTable.choiceMonomial G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample choice)

def rightTermIntegral (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal S)
    (sample : S.binary.Assignment) (choice : Fin S.count -> Option (Fin (channelCount w))) : Int :=
  (PairRootChannels.prior G.binary (channelCount w)).signedMass
    (HedgeChannelTable.choiceMonomial G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample choice)

private theorem leftTermIntegral_zero_outside (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (leftTables w child).expansionChoicesUnder none)) (excluded : choice ∉ leftSurvivors w) :
    leftTermIntegral w rich smallSignal backgroundSignal sample choice = 0 := by
  by_cases zero : leftTermIntegral w rich smallSignal backgroundSignal sample choice = 0
  · exact zero
  · apply False.elim
    apply excluded
    rcases left_nonzero_choice w rich smallSignal backgroundSignal sample choice member zero with common | main
    · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
        ⟨backgroundMask w choice, (masks_member_iff _ _).mpr common.2, common.1.symm⟩))
    · rcases main with ⟨index, same, subset⟩
      exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨index, List.mem_finRange index, List.mem_map.mpr
          ⟨remainingBackgroundMask w w.large choice, (masks_member_iff _ _).mpr subset, same.symm⟩⟩))

private theorem rightTermIntegral_zero_outside (w : HedgeWitness G q)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment)
    (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (rightTables w child).expansionChoicesUnder none)) (excluded : choice ∉ rightSurvivors w) :
    rightTermIntegral w smallSignal backgroundSignal sample choice = 0 := by
  by_cases zero : rightTermIntegral w smallSignal backgroundSignal sample choice = 0
  · exact zero
  · apply False.elim
    apply excluded
    rcases right_nonzero_choice w smallSignal backgroundSignal sample choice member zero with common | main
    · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
        ⟨backgroundMask w choice, (masks_member_iff _ _).mpr common.2, common.1.symm⟩))
    · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
        ⟨remainingBackgroundMask w w.small choice, (masks_member_iff _ _).mpr main.2, main.1.symm⟩))

/-- The complete left expansion is exactly the canonical survivor sum.
Every original term was retained until actual integration proved it zero;
the canonical list is proved included and repetition-free.  The finite
integer zero test in the support proof introduces no Prop excluded middle. -/
theorem left_expandedIntegral_survivors (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) :
    HedgeChannelTable.expandedIntegral G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample =
      ((leftSurvivors w).map (leftTermIntegral w rich smallSignal backgroundSignal sample)).sum :=
  (HedgeChannelTable.expandedIntegral_eq_sum G (channelCount w) (leftTables w)
    (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample).trans
    (FiniteSupportedSum.sum_eq_of_zero_outside _ _
      (FiniteProduct.enumeration_nodup S.count (fun _ => Option (Fin (channelCount w))) _
        (fun _ => inferInstance) (coefficientChoices_nodup _ _ _ _ _))
      (leftSurvivors_nodup w) (leftSurvivors_member w)
      (leftTermIntegral w rich smallSignal backgroundSignal sample)
      (leftTermIntegral_zero_outside w rich smallSignal backgroundSignal sample))

theorem right_expandedIntegral_survivors (w : HedgeWitness G q)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) :
    HedgeChannelTable.expandedIntegral G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample =
      ((rightSurvivors w).map (rightTermIntegral w smallSignal backgroundSignal sample)).sum :=
  (HedgeChannelTable.expandedIntegral_eq_sum G (channelCount w) (rightTables w)
    (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample).trans
    (FiniteSupportedSum.sum_eq_of_zero_outside _ _
      (FiniteProduct.enumeration_nodup S.count (fun _ => Option (Fin (channelCount w))) _
        (fun _ => inferInstance) (coefficientChoices_nodup _ _ _ _ _))
      (rightSurvivors_nodup w) (rightSurvivors_member w)
      (rightTermIntegral w smallSignal backgroundSignal sample)
      (rightTermIntegral_zero_outside w smallSignal backgroundSignal sample))

/-- The reduction also presents the actual nonnegative likelihood
numerator.  Integers remain an exact embedding of that numerator, and the
original common denominator is unchanged by deleting zero integrals. -/
theorem left_integratedNumerator_survivors (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) :
    (HedgeChannelTable.integratedNumerator G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample : Int) =
      ((leftSurvivors w).map (leftTermIntegral w rich smallSignal backgroundSignal sample)).sum :=
  (HedgeChannelTable.integratedNumerator_expansion G (channelCount w) (leftTables w)
    (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample).trans
    (left_expandedIntegral_survivors w rich smallSignal backgroundSignal sample)

theorem right_integratedNumerator_survivors (w : HedgeWitness G q)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) :
    (HedgeChannelTable.integratedNumerator G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample : Int) =
      ((rightSurvivors w).map (rightTermIntegral w smallSignal backgroundSignal sample)).sum :=
  (HedgeChannelTable.integratedNumerator_expansion G (channelCount w) (rightTables w)
    (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample).trans
    (right_expandedIntegral_survivors w smallSignal backgroundSignal sample)

/-! ## Matching the actual common background contribution -/

private theorem backgroundMonomials_equal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) (mask : NodeSet S)
    (shared : (PairRootChannels.extension G.binary (channelCount w)).Assignment) :
    HedgeChannelTable.choiceMonomial G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample (backgroundChoice w mask) shared =
    HedgeChannelTable.choiceMonomial G (channelCount w) (rightTables w)
      (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample (backgroundChoice w mask) shared := by
  apply FiniteProduct.iProduct_congr
  intro child
  cases chosen : mask child with
  | false =>
      simp only [backgroundChoice, chosen, Bool.false_eq_true, if_false,
        BooleanChannelTable.expansionTermUnder, BooleanChannelTable.expansionTerm]
      exact congrArg (fun capacity : Nat => (capacity : Int)) (capacities_equal w child)
  | true =>
      have amplitudes : (leftTables w child).amplitude (backgroundChannel w child) =
          (rightTables w child).amplitude (backgroundChannel w child) := by
        change HedgeChannelCoefficients.scale (channelCount w) ^
            HedgeChannelCoefficients.rowExponent S.count (leftAnchors w) (leftDeficits w) child (backgroundChannel w child) =
          HedgeChannelCoefficients.scale (channelCount w) ^
            HedgeChannelCoefficients.rowExponent S.count (rightAnchors w) (rightDeficits w) child (backgroundChannel w child)
        simp only [HedgeChannelCoefficients.rowExponent, leftAnchors, rightAnchors, role_backgroundChannel]
      have signals : leftSignals w rich smallSignal backgroundSignal child
          (fun parent _edge => sample parent) (fun root _incident => shared root) (backgroundChannel w child) =
          rightSignals w smallSignal backgroundSignal child
            (fun parent _edge => sample parent) (fun root _incident => shared root) (backgroundChannel w child) := by
        simp only [leftSignals, rightSignals, HedgeChannelTable.incidenceSignals,
          leftParentSignal, rightParentSignal, role_backgroundChannel, backgroundNodes_equal]
      simp only [backgroundChoice, chosen, if_true, BooleanChannelTable.expansionTermUnder,
        BooleanChannelTable.expansionTerm, amplitudes, signals]

/-- Every background-only integral matches on the same real prior, with
the same actual row capacities, amplitudes, typed parent signals and local
incidence.  Equality is not inferred just from matching support or means. -/
theorem backgroundTermIntegrals_equal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) (mask : NodeSet S) :
    leftTermIntegral w rich smallSignal backgroundSignal sample (backgroundChoice w mask) =
      rightTermIntegral w smallSignal backgroundSignal sample (backgroundChoice w mask) :=
  FiniteProbRecord.signedAtomMass_congr (PairRootChannels.prior G.binary (channelCount w)).atoms _ _
    (backgroundMonomials_equal w rich smallSignal backgroundSignal sample mask)

/-- Consequently the entire common block of survivor terms agrees.
Every permitted background interaction is summed, not just its marginals. -/
theorem commonTermIntegrals_equal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) :
    ((commonChoices w).map (leftTermIntegral w rich smallSignal backgroundSignal sample)).sum =
      ((commonChoices w).map (rightTermIntegral w smallSignal backgroundSignal sample)).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro choice member
  rcases List.mem_map.mp member with ⟨mask, _maskMember, same⟩
  rw [← same]
  exact backgroundTermIntegrals_equal w rich smallSignal backgroundSignal sample mask

/-- Exact remaining observational-assembly obligation at any full sample:
the summed full large-channel integrals must equal the summed full small-
channel integrals.  All other actual terms have either cancelled by proved
integration or matched in the complete common block above.  This equivalence
does not assert that the remaining full-channel sums have already matched. -/
theorem expandedIntegrals_eq_iff_fullSums (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (sample : S.binary.Assignment) :
    (HedgeChannelTable.expandedIntegral G (channelCount w) (leftTables w)
      (leftSignals w rich smallSignal backgroundSignal) (fun _ => none) sample =
      HedgeChannelTable.expandedIntegral G (channelCount w) (rightTables w)
        (rightSignals w smallSignal backgroundSignal) (fun _ => none) sample) ↔
    (((leftFullChoices w).map (leftTermIntegral w rich smallSignal backgroundSignal sample)).sum =
      ((rightFullChoices w).map (rightTermIntegral w smallSignal backgroundSignal sample)).sum) := by
  rw [left_expandedIntegral_survivors, right_expandedIntegral_survivors]
  simp only [leftSurvivors, rightSurvivors, List.map_append, List.sum_append]
  rw [commonTermIntegrals_equal]
  constructor
  · exact Int.add_left_cancel
  · intro same
    exact congrArg (_ + ·) same

end HedgeChannelInstallation
end Causality
end Thesis
