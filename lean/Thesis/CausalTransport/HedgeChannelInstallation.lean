import Thesis.CausalTransport.HedgeChannelCharacters
import Thesis.CausalTransport.HedgeChannelCoefficients
import Thesis.Probability.FiniteProductSupport

namespace Thesis
namespace Causality
namespace HedgeChannelInstallation

open Probability

/-!
# Installing the independent-channel family on an arbitrary hedge

The coefficient identities do not themselves specify graph-compatible
models.  This module installs their finite channel slots, supports, anchors,
and local parent signals for every supplied hedge.  The left model has one
large-forest channel for each outer-background mask.  The right model has
one small-forest channel.  Both have the same singleton background channels
outside the small forest, and retain the same complete pair-root alphabet.

Masks enumerate only genuine subsets of `large \\ small`.  At every other
observed coordinate the sole local choice is `false`.  Enumerating all bits
and then masking them would repeat each outer subset, silently multiplying
the large contribution; no such redundant masks are present here.  The
construction and its repetition-free proof are symbolic: an exponential
concrete support is not reduced by a proof-time decision procedure.

Every anchor is already constructive hedge data.  Large channels use the
stored action vertex; the small channel uses its computed common root.
Inactive slots have empty supports, rather than disappearing from one
model's source space.  Common capacities and full Boolean observed support
follow from the explicit power construction without a smallness premise.

The supplied small and background parent signals remain arbitrary typed
local functions.  Distinguished original labels provide an explicit bridge
to Boolean parent values; they are not chosen representatives.  The large
signals use the previously proved character correction on the actual kept
arrows, so routes leaving and re-entering the forest are not prohibited.

This is an actual model-family installation, not a completeness theorem.
`HedgeChannelObservational` separately evaluates and reindexes its complete
factual expansion, proving equality of every observed event.  Selecting an
action-avoiding outcome flow and proving its original-query marginal gap
remain separate obligations.  Positivity and compatibility are not used as
substitutes for either observed-law equality or interventional separation.
-/

variable {S : ObservedSignature.{0}} {G : ObservedGraph S} {q : JointKernelQuery S}

/-! ## Complete, nonredundant outer masks -/

/-- Allowed mask bits at an original observed coordinate.  The singleton
choice off the outer forest is essential to avoiding duplicate masks. -/
def maskChoices (outer : NodeSet S) (node : Fin S.count) : List Bool :=
  if outer node then [false, true] else [false]

/-- The literal finite product of the allowed local mask lists. -/
def masks (outer : NodeSet S) : List (NodeSet S) :=
  FiniteProduct.enumeration S.count (fun _ => Bool) (maskChoices outer)

/-- A mask occurs exactly when it is an outer subset.  Completeness is
relative to the permitted coordinate lists, not to all Boolean vectors. -/
theorem masks_member_iff (outer mask : NodeSet S) :
    mask ∈ masks outer ↔ NodeSet.Subset mask outer := by
  constructor
  · intro member node selected
    have localMember := FiniteProduct.enumeration_coordinate_mem S.count
      (fun _ => Bool) (maskChoices outer) mask member node
    cases inside : outer node with
    | true => rfl
    | false =>
        simp only [maskChoices, inside, Bool.false_eq_true, if_false,
          List.mem_singleton] at localMember
        exact False.elim (Bool.false_ne_true (localMember.symm.trans selected))
  · intro subset
    apply FiniteProduct.enumeration_mem_of_coordinate_mem
    intro node
    cases inside : outer node with
    | true => cases mask node <;> simp only [maskChoices, inside, if_true, List.mem_cons, List.not_mem_nil] <;> simp
    | false =>
        have absent : mask node = false := by
          cases selected : mask node with
          | false => rfl
          | true => exact False.elim (Bool.false_ne_true (inside.symm.trans (subset node selected)))
        simp only [maskChoices, inside, Bool.false_eq_true, if_false, List.mem_singleton, absent]

/-- Every permitted mask is listed once.  Only explicit finite Boolean
equality is supplied to the dependent product's uniqueness theorem. -/
theorem masks_nodup (outer : NodeSet S) : (masks outer).Nodup := by
  apply FiniteProduct.enumeration_nodup S.count (fun _ => Bool) (maskChoices outer)
    (fun _ => inferInstance)
  intro node
  cases chosen : outer node <;> simp only [maskChoices, chosen] <;> decide

/-- The empty mask supplies an explicit member even at zero outer size. -/
theorem empty_mask_member (outer : NodeSet S) : NodeSet.empty ∈ masks outer :=
  (masks_member_iff outer NodeSet.empty).mpr
    (fun _ selected => False.elim (Bool.false_ne_true selected))

private theorem members_length_le (nodes : NodeSet S) : (NodeSet.members nodes).length <= S.count :=
  Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (NodeSet.length_enumerated S))

private theorem members_length_le_of_subset (smaller larger : NodeSet S)
    (subset : NodeSet.Subset smaller larger) :
    (NodeSet.members smaller).length <= (NodeSet.members larger).length := by
  have intersection : NodeSet.inter larger smaller = smaller := by
    funext node
    cases selected : smaller node with
    | false => simp only [NodeSet.inter, selected, Bool.and_false]
    | true => simp only [NodeSet.inter, selected, subset node selected, Bool.and_self]
  rw [← intersection, NodeSet.members_inter]
  exact List.length_filter_le _ _

/-- Exactly the outer-only vertices of the original hedge. -/
def outer (w : HedgeWitness G q) : NodeSet S := NodeSet.diff w.large w.small

/-- A finite mask slot carries its actual listed outer subset.  No search
result or representative is selected from an existential proposition. -/
def selected (w : HedgeWitness G q) (index : Fin (masks (outer w)).length) : NodeSet S :=
  (masks (outer w)).get index

theorem selected_subset (w : HedgeWitness G q) (index : Fin (masks (outer w)).length) :
    NodeSet.Subset (selected w index) (outer w) :=
  (masks_member_iff (outer w) _).mp (List.get_mem _ index)

/-- The degree bound is the original observed count.  Both the complete
outer set and every listed selection fit without a further readiness test. -/
theorem outer_degree_bound (w : HedgeWitness G q) :
    (NodeSet.members (outer w)).length <= S.count := members_length_le (outer w)

theorem selected_degree_bound (w : HedgeWitness G q) (index : Fin (masks (outer w)).length) :
    (NodeSet.members (selected w index)).length <= (NodeSet.members (outer w)).length :=
  members_length_le_of_subset _ _ (selected_subset w index)

/-! ## One common finite channel alphabet -/

/-- Large mask slots, one small slot, and one background slot per original
node.  Background slots inside the small forest will be inactive on both
sides; keeping them preserves a literal common source alphabet. -/
def channelCount (w : HedgeWitness G q) : Nat := (masks (outer w)).length + 1 + S.count

/-- The three meanings of a slot in the shared finite channel alphabet.
Only the large role carries a mask; a background role names its actual row. -/
inductive Role (w : HedgeWitness G q) where
  | large (index : Fin (masks (outer w)).length)
  | small
  | background (node : Fin S.count)

/-- Decode a channel by its three consecutive finite blocks.  The final
index bound follows from the original channel bound, not from choice. -/
def role (w : HedgeWitness G q) (channel : Fin (channelCount w)) : Role w :=
  if large : channel.val < (masks (outer w)).length then .large ⟨channel.val, large⟩
  else if small : channel.val = (masks (outer w)).length then .small
  else .background ⟨channel.val - ((masks (outer w)).length + 1), by
    have bound := channel.isLt
    unfold channelCount at bound
    omega⟩

/-- Explicit inclusion of the first, mask-indexed block. -/
def largeChannel (w : HedgeWitness G q) (index : Fin (masks (outer w)).length) : Fin (channelCount w) :=
  ⟨index.val, by have bound := index.isLt; unfold channelCount; omega⟩

/-- The sole slot immediately after the complete large-mask block. -/
def smallChannel (w : HedgeWitness G q) : Fin (channelCount w) :=
  ⟨(masks (outer w)).length, by unfold channelCount; omega⟩

/-- The final block retains one slot per original observed vertex. -/
def backgroundChannel (w : HedgeWitness G q) (node : Fin S.count) : Fin (channelCount w) :=
  ⟨(masks (outer w)).length + 1 + node.val, by have bound := node.isLt; unfold channelCount; omega⟩

theorem role_largeChannel (w : HedgeWitness G q) (index : Fin (masks (outer w)).length) :
    role w (largeChannel w index) = .large index := by
  unfold role largeChannel
  rw [dif_pos index.isLt]

theorem role_smallChannel (w : HedgeWitness G q) : role w (smallChannel w) = .small := by
  unfold role smallChannel
  rw [dif_neg (Nat.lt_irrefl _), dif_pos rfl]

theorem role_backgroundChannel (w : HedgeWitness G q) (node : Fin S.count) :
    role w (backgroundChannel w node) = .background node := by
  unfold role backgroundChannel
  rw [dif_neg (show ¬ ((masks (outer w)).length + 1 + node.val < (masks (outer w)).length) by omega),
    dif_neg (show (masks (outer w)).length + 1 + node.val ≠ (masks (outer w)).length by omega)]
  congr 1
  apply Fin.ext
  simp only [Nat.add_sub_cancel_left]

/-- Reassemble the three consecutive blocks without choosing an inverse
of the decoder.  The two round trips below keep slot identity explicit for
the complete row-choice survivor calculation. -/
def channelOfRole (w : HedgeWitness G q) : Role w -> Fin (channelCount w)
  | .large index => largeChannel w index
  | .small => smallChannel w
  | .background node => backgroundChannel w node

theorem channelOfRole_role (w : HedgeWitness G q) (channel : Fin (channelCount w)) :
    channelOfRole w (role w channel) = channel := by
  unfold role
  split
  · apply Fin.ext
    rfl
  · split
    · next same => exact Fin.ext same.symm
    · next outside different =>
        apply Fin.ext
        change (masks (outer w)).length + 1 + (channel.val - ((masks (outer w)).length + 1)) = channel.val
        omega

theorem role_channelOfRole (w : HedgeWitness G q) (tag : Role w) :
    role w (channelOfRole w tag) = tag := by
  cases tag with
  | large index => exact role_largeChannel w index
  | small => exact role_smallChannel w
  | background node => exact role_backgroundChannel w node

/-! ## Supports and anchored exponents -/

/-- Common background support, including its intentional empty boundary
inside the small forest.  A singleton channel has zero pair incidence and
therefore realizes an ordinary local noisy background, not a shared switch. -/
def backgroundNodes (w : HedgeWitness G q) (node : Fin S.count) : NodeSet S :=
  if w.small node then NodeSet.empty else NodeSet.singleton node

def leftNodes (w : HedgeWitness G q) (channel : Fin (channelCount w)) : NodeSet S :=
  match role w channel with
  | .large _ => w.large
  | .small => NodeSet.empty
  | .background node => backgroundNodes w node

def rightNodes (w : HedgeWitness G q) (channel : Fin (channelCount w)) : NodeSet S :=
  match role w channel with
  | .large _ => NodeSet.empty
  | .small => w.small
  | .background node => backgroundNodes w node

/-- All large channels are anchored at the stored intervention vertex. -/
def leftAnchors (w : HedgeWitness G q) (channel : Fin (channelCount w)) : Option (Fin S.count) :=
  match role w channel with
  | .large _ => some w.actionSeed
  | _ => none

/-- The small anchor is the computed common root, already known to be in
the small forest.  No root is extracted from a Prop existential. -/
def rightAnchors (w : HedgeWitness G q) (channel : Fin (channelCount w)) : Option (Fin S.count) :=
  match role w channel with
  | .small => some w.actionRoot
  | _ => none

def leftDeficits (w : HedgeWitness G q) (channel : Fin (channelCount w)) : Nat :=
  match role w channel with
  | .large index => (NodeSet.members (selected w index)).length
  | _ => 0

def rightDeficits (w : HedgeWitness G q) (channel : Fin (channelCount w)) : Nat :=
  match role w channel with
  | .small => (NodeSet.members (outer w)).length
  | _ => 0

theorem leftNodes_largeChannel (w : HedgeWitness G q) (index : Fin (masks (outer w)).length) :
    leftNodes w (largeChannel w index) = w.large := by rw [leftNodes, role_largeChannel]

theorem rightNodes_largeChannel (w : HedgeWitness G q) (index : Fin (masks (outer w)).length) :
    rightNodes w (largeChannel w index) = NodeSet.empty := by rw [rightNodes, role_largeChannel]

theorem leftNodes_smallChannel (w : HedgeWitness G q) : leftNodes w (smallChannel w) = NodeSet.empty := by
  rw [leftNodes, role_smallChannel]

theorem rightNodes_smallChannel (w : HedgeWitness G q) : rightNodes w (smallChannel w) = w.small := by
  rw [rightNodes, role_smallChannel]

/-- Every background slot has the identical support on both sides,
including the slots intentionally left inactive in the small forest. -/
theorem backgroundNodes_equal (w : HedgeWitness G q) (node : Fin S.count) :
    leftNodes w (backgroundChannel w node) = rightNodes w (backgroundChannel w node) := by
  rw [leftNodes, rightNodes, role_backgroundChannel]

/-- Deficit bounds are intrinsic to the installed mask and forest, so the
natural-power matching identities do not silently use truncated exponents. -/
theorem leftDeficits_bound (w : HedgeWitness G q) (channel : Fin (channelCount w)) :
    leftDeficits w channel <= S.count := by
  unfold leftDeficits
  cases role w channel with
  | large index => exact Nat.le_trans (selected_degree_bound w index) (outer_degree_bound w)
  | small => exact Nat.zero_le _
  | background _ => exact Nat.zero_le _

theorem rightDeficits_bound (w : HedgeWitness G q) (channel : Fin (channelCount w)) :
    rightDeficits w channel <= S.count := by
  unfold rightDeficits
  cases role w channel with
  | large _ => exact Nat.zero_le _
  | small => exact outer_degree_bound w
  | background _ => exact Nat.zero_le _

/-! ## Typed local signals and actual positive models -/

/-- Only declared Boolean parents are read.  These functions will later
be instantiated with the small-side and common outcome-flow equations. -/
abbrev ParentSignal (S : ObservedSignature.{0}) :=
  (child : Fin S.count) -> S.binary.ParentValues child -> Bool

private def originalSignal (rich : ObservedSignature.ValueRich S) (signal : ParentSignal S)
    (child : Fin S.count) (parents : S.ParentValues child) : Bool :=
  signal child (fun parent edge => hedgeIsSecond rich parent (parents parent edge))

/-- The large correction is evaluated on the explicit encoding of the
typed Boolean parents.  The old character theorem thus remains attached to
the original hedge and kept edges; mechanisms never read a full assignment. -/
def largeParentSignal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (index : Fin (masks (outer w)).length)
    (child : Fin S.count) (parents : S.binary.ParentValues child) : Bool :=
  w.channelParentSignal rich (selected w index) (originalSignal rich smallSignal)
    (originalSignal rich backgroundSignal) child
    (fun parent edge => BinaryEncoding.value rich parent (parents parent edge))

private theorem bit_encoded (rich : ObservedSignature.ValueRich S) (node : Fin S.count) (bit : Bool) :
    hedgeIsSecond rich node (BinaryEncoding.value rich node bit) = bit :=
  BinaryEncoding.bit_value rich node bit

/-- The installed typed Boolean signal has precisely the existing hedge
character identity.  This verifies the parent-label bridge, including kept
arrows entering unselected or small vertices; no global sample is available
to a row mechanism merely because it appears in this theorem. -/
theorem largeParentSignal_factorization (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (index : Fin (masks (outer w)).length)
    (sample : S.binary.Assignment) :
    hedgeNodeXor w.large (fun child => Bool.xor (sample child)
      (largeParentSignal w rich smallSignal backgroundSignal index child (fun parent _edge => sample parent))) =
      Bool.xor
        (hedgeNodeXor w.small (fun child => Bool.xor (sample child)
          (smallSignal child (fun parent _edge => sample parent))))
        (hedgeNodeXor (selected w index) (fun child => Bool.xor (sample child)
          (backgroundSignal child (fun parent _edge => sample parent)))) := by
  have factorization := w.channelCharacter_factorization rich (selected w index) (selected_subset w index)
    (originalSignal rich smallSignal) (originalSignal rich backgroundSignal) (BinaryEncoding.assignment rich sample)
  simpa only [largeParentSignal, BinaryEncoding.assignment, originalSignal, bit_encoded] using factorization

def leftParentSignal (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (child : Fin S.count)
    (parents : S.binary.ParentValues child) (channel : Fin (channelCount w)) : Bool :=
  match role w channel with
  | .large index => largeParentSignal w rich smallSignal backgroundSignal index child parents
  | .small => false
  | .background _ => backgroundSignal child parents

def rightParentSignal (w : HedgeWitness G q)
    (smallSignal backgroundSignal : ParentSignal S) (child : Fin S.count)
    (parents : S.binary.ParentValues child) (channel : Fin (channelCount w)) : Bool :=
  match role w channel with
  | .large _ => false
  | .small => smallSignal child parents
  | .background _ => backgroundSignal child parents

def leftTables (w : HedgeWitness G q) :=
  HedgeChannelCoefficients.tables (channelCount w) S.count (leftNodes w) (leftAnchors w) (leftDeficits w)

def rightTables (w : HedgeWitness G q) :=
  HedgeChannelCoefficients.tables (channelCount w) S.count (rightNodes w) (rightAnchors w) (rightDeficits w)

/-- Actual local centre vectors, on the original incident pair roots. -/
def leftSignals (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) : HedgeChannelTable.Signals G (channelCount w) :=
  HedgeChannelTable.incidenceSignals G (channelCount w) (leftNodes w)
    (leftParentSignal w rich smallSignal backgroundSignal)

def rightSignals (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal S) :
    HedgeChannelTable.Signals G (channelCount w) :=
  HedgeChannelTable.incidenceSignals G (channelCount w) (rightNodes w)
    (rightParentSignal w smallSignal backgroundSignal)

/-- The left SCM installs all large mask channels at actual independent
pair roots.  Positive private rows have already been constructed exactly. -/
def leftModel (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) : ExactModel S.binary :=
  HedgeChannelCoefficients.model G (channelCount w) S.count (leftNodes w) (leftAnchors w) (leftDeficits w)
    (leftParentSignal w rich smallSignal backgroundSignal)

/-- The right SCM uses the same channel alphabet and ordinary backgrounds,
with its own small channel active instead of the large mask channels. -/
def rightModel (w : HedgeWitness G q) (smallSignal backgroundSignal : ParentSignal S) : ExactModel S.binary :=
  HedgeChannelCoefficients.model G (channelCount w) S.count (rightNodes w) (rightAnchors w) (rightDeficits w)
    (rightParentSignal w smallSignal backgroundSignal)

/-- Full original projected-graph compatibility of both actual models.
Unused slots do not enlarge latent incidence or drop an original edge. -/
theorem models_compatible (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) :
    Compatible (leftModel w rich smallSignal backgroundSignal) G.binary ∧
      Compatible (rightModel w smallSignal backgroundSignal) G.binary :=
  ⟨HedgeChannelCoefficients.model_compatible G _ _ _ _ _ _,
    HedgeChannelCoefficients.model_compatible G _ _ _ _ _ _⟩

/-- Every full Boolean observed sample has positive probability on both
sides, for all typed local signals and every arbitrary supplied hedge. -/
theorem models_positive (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) :
    ObservationallyPositive (leftModel w rich smallSignal backgroundSignal) ∧
      ObservationallyPositive (rightModel w smallSignal backgroundSignal) :=
  ⟨HedgeChannelCoefficients.model_positive G _ _ _ _ _ _,
    HedgeChannelCoefficients.model_positive G _ _ _ _ _ _⟩

/-- Exact equality of every actual row capacity, not merely equivalent
normalized probabilities.  This is the denominator premise for the later
complete-likelihood observational and event-gap theorems. -/
theorem capacities_equal (w : HedgeWitness G q) (child : Fin S.count) :
    (leftTables w child).capacity = (rightTables w child).capacity :=
  HedgeChannelCoefficients.tables_capacities_equal _ _ _ _ _ _ _ _ child

/-! ## Installed connected channels and the original action cut -/

private theorem connected_binary {nodes : NodeSet S} {first second : Fin S.count}
    (path : BidirectedConnectedWithin G nodes first second) :
    BidirectedConnectedWithin G.binary nodes first second := by
  induction path with
  | refl inside => exact .refl inside
  | tail _previous inside edge inductionHypothesis => exact .tail inductionHypothesis inside edge

private theorem component_binary (nodes : NodeSet S) (component : BidirectedComponent G nodes) :
    BidirectedComponent G.binary nodes :=
  ⟨component.1, fun first second firstInside secondInside =>
    connected_binary (component.2 first second firstInside secondInside)⟩

/-- Boolean encoding changes labels, not connected forest supports. -/
theorem large_component (w : HedgeWitness G q) : BidirectedComponent G.binary w.large :=
  component_binary w.large w.large_forest.component

theorem small_component (w : HedgeWitness G q) : BidirectedComponent G.binary w.small :=
  component_binary w.small w.small_forest.component

/-- Every term of the installed left likelihood that selects a large
channel cancels when the stored original action vertex is forced.  All
other forced vertices, background selections and channel interactions are
retained.  In particular, composite actions need no seed-or-sink restriction.
This is term cancellation, not yet equality of the two whole likelihoods or
a projected original-outcome gap. -/
theorem left_large_term_zero_of_action (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (leftTables w child).expansionChoicesUnder (target child)))
    (index : Fin (masks (outer w)).length) (fixed : Bool) (forced : target w.actionSeed = some fixed)
    (pivot : Fin S.count) (picked : choice pivot = some (largeChannel w index)) :
    (PairRootChannels.prior G.binary (channelCount w)).signedMass
      (HedgeChannelTable.choiceMonomial G (channelCount w) (leftTables w)
        (leftSignals w rich smallSignal backgroundSignal) target sample choice) = 0 := by
  apply HedgeChannelTable.choiceMonomial_signedMass_zero_of_forced G (channelCount w)
    (leftTables w) (leftNodes w) (leftParentSignal w rich smallSignal backgroundSignal)
    (HedgeChannelCoefficients.tables_channel_allowed _ _ _ _ _)
    target sample choice member (largeChannel w index)
  · rw [leftNodes_largeChannel]
    exact large_component w
  · rw [leftNodes_largeChannel]
    exact w.actionSeed_in_large
  · exact forced
  · exact picked

/-- Distinct large mask channels cannot both occur in a nonzero term of
the actual installed likelihood.  Each selected connected channel must be
fully selected, but both would require the same row at the common root.
Singleton backgrounds are deliberately not subjected to a false common-
pivot premise: they may coexist with a full main channel outside its support.
This rules out mixed large-channel interactions by integration, rather than
discarding them from the complete expansion at its definition. -/
theorem left_nonzero_large_unique (w : HedgeWitness G q) (rich : ObservedSignature.ValueRich S)
    (smallSignal backgroundSignal : ParentSignal S) (target : Fin S.count -> Option Bool)
    (sample : S.binary.Assignment) (choice : Fin S.count -> Option (Fin (channelCount w)))
    (member : choice ∈ FiniteProduct.enumeration S.count (fun _ => Option (Fin (channelCount w)))
      (fun child => (leftTables w child).expansionChoicesUnder (target child)))
    (nonzero : (PairRootChannels.prior G.binary (channelCount w)).signedMass
      (HedgeChannelTable.choiceMonomial G (channelCount w) (leftTables w)
        (leftSignals w rich smallSignal backgroundSignal) target sample choice) ≠ 0)
    (first second : Fin (masks (outer w)).length) (firstRow secondRow : Fin S.count)
    (firstPick : choice firstRow = some (largeChannel w first))
    (secondPick : choice secondRow = some (largeChannel w second)) : first = second := by
  have full : forall index row, choice row = some (largeChannel w index) ->
      HedgeChannelTable.selectedNodes choice (largeChannel w index) = leftNodes w (largeChannel w index) := by
    intro index row picked
    apply HedgeChannelTable.choiceMonomial_nonzero_full G (channelCount w) (leftTables w)
      (leftNodes w) (leftParentSignal w rich smallSignal backgroundSignal)
      (HedgeChannelCoefficients.tables_channel_allowed _ _ _ _ _) target sample choice member nonzero
      (largeChannel w index)
    · rw [leftNodes_largeChannel]
      exact large_component w
    · exact picked
  have common : forall index, leftNodes w (largeChannel w index) w.actionRoot = true := by
    intro index
    rw [leftNodes_largeChannel]
    exact w.actionRoot_in_large
  have same := HedgeChannelTable.selectedNodes_full_unique (leftNodes w) choice
    (largeChannel w first) (largeChannel w second) w.actionRoot (common first) (common second)
    (full first firstRow firstPick) (full second secondRow secondPick)
  exact Fin.ext (congrArg (fun channel : Fin (channelCount w) => channel.val) same)

/-- The installed mask exponent meets the coefficient theorem's complete
outer bound, without a graph-specific readiness premise.  Identifying these
abstract coefficients with the surviving actual row products is still a
separate row-product calculation and full-channel sum identity. -/
theorem mask_fullCoefficient_match (w : HedgeWitness G q) (smallOthers : Nat)
    (index : Fin (masks (outer w)).length) :
    HedgeChannelCoefficients.fullCoefficient (channelCount w) S.count
      (smallOthers + (NodeSet.members (outer w)).length) (NodeSet.members (selected w index)).length =
      HedgeChannelCoefficients.fullCoefficient (channelCount w) S.count smallOthers
        (NodeSet.members (outer w)).length *
      HedgeChannelCoefficients.outerCoefficient (channelCount w) S.count
        (NodeSet.members (outer w)).length (NodeSet.members (selected w index)).length :=
  HedgeChannelCoefficients.fullCoefficient_match _ _ _ _ _
    (outer_degree_bound w) (selected_degree_bound w index)

end HedgeChannelInstallation
end Causality
end Thesis
