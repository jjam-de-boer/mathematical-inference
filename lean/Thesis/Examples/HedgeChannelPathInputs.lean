import Thesis.CausalTransport.HedgeChannelPathInputs
import Thesis.Examples.ActivePathPairRoots

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentHedgeChannelPathInputs

open PathSpecification Probability FiniteBooleanInteraction
open HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# Actual path masks, original-root cancellation, and an omitted observed fork

The first regression reuses the certified reversed-label path `L <- U -> R
-> Y`.  No hand-written masks are supplied: `LinearSignal.ofActivePath`
constructs them from that actual list and its exact cut graph.  Its masks
agree with the earlier manually displayed legal signal.  Whole-point phase
conservation is then obtained from the general installed-path theorem and a
literal endpoint-boundary calculation.  The earlier displayed odd direction
also holds for this constructed signal.

The independent four-vertex path is `A <- F -> B -> Y`.  `F` is a genuine
observed fork: its two outgoing contributions cancel but its own row must
not be selected.  The original graph also has the off-path arrow `F -> Y`
and a bidirected pair `F <-> Y`.  Neither is read by this path's signal.
Thus the tests distinguish actual consecutive inputs from all available
inputs, and actual head rows from all observed path vertices.

Both fixtures have original three-valued alphabets.  These algebraic tests
do not assert that an arbitrary conditional terminal already has the needed
collider activation and complete Small-forest interaction.
-/

namespace ReversedPair

open CurrentActivePathPairRoots

/-- The new construction receives the actual active path, not its manually
chosen masks or a phase-conservation premise. -/
def constructedSignal : LinearSignal graph := .ofActivePath actualPath

theorem constructed_parent_masks (child parent : Fin signature.count) :
    constructedSignal.parentMask child parent = signalData.parentMask child parent := by
  decide +kernel +revert

theorem constructed_root_masks (child : Fin signature.count) (root : Fin (pairRootCount graph.binary)) :
    constructedSignal.rootMask child root = signalData.rootMask child root := by
  decide +kernel +revert

private theorem constructedSignal_eq : constructedSignal = signalData := by
  have parents := funext (fun child => funext (constructed_parent_masks child))
  have roots := funext (fun child => funext (constructed_root_masks child))
  change LinearSignal.mk constructedSignal.parentMask constructedSignal.rootMask =
    LinearSignal.mk signalData.parentMask signalData.rootMask
  rw [parents, roots]

theorem actual_heads (child : Fin signature.count) : ActivePathInput.headRows graph cut actualPath.nodes child = true := by
  decide +kernel +revert

/-- Original reserved-input cancellation is an instance of the new general
path theorem, rather than another finite decision of the coefficient. -/
theorem actual_root_conservation :
    constructedSignal.forestRootCoefficient (ActivePathInput.headRows graph cut actualPath.nodes) originalRoot = false :=
  LinearSignal.ofActivePath_forestRootCoefficient actualPath originalRoot

theorem actual_observed_boundary (child : Fin signature.count) :
    ActivePathInput.observedBoundary graph cut actualPath.nodes child = endpoints child := by
  decide +kernel +revert

theorem actual_complete_phase (point : Cube graph) :
    (constructedSignal.forestPhase NodeSet.full).value point = (maskPhase _ (cubeMask graph endpoints)).value point := by
  have allHeads : ActivePathInput.headRows graph cut actualPath.nodes = NodeSet.full := funext actual_heads
  rw [← allHeads]
  change ((LinearSignal.ofActivePath actualPath).forestPhase _).value point = _
  rw [LinearSignal.ofActivePath_forestPhase]
  exact congrArg (fun mask => (maskPhase _ (cubeMask graph mask)).value point) (funext actual_observed_boundary)

theorem actual_odd_source : (constructedSignal.rowPhase leftNode).value direction = true ∧
    (constructedSignal.rowPhase rightNode).value direction = false ∧
    (constructedSignal.rowPhase outcome).value direction = false := by
  rw [constructedSignal_eq]
  exact actual_direction_rows

end ReversedPair

namespace ObservedFork

def signature : ObservedSignature where
  count := 4
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide ((parent.val = 0 ∧ (child.val = 1 ∨ child.val = 2 ∨ child.val = 3)) ∨
    (parent.val = 2 ∧ child.val = 3))
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def fork : Fin signature.count := ⟨0, by decide⟩
def source : Fin signature.count := ⟨1, by decide⟩
def middle : Fin signature.count := ⟨2, by decide⟩
def outcome : Fin signature.count := ⟨3, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun left right => decide ((left.val = 0 ∧ right.val = 3) ∨ (left.val = 3 ∧ right.val = 0))
  bidirected_symmetric := by
    intro left right edge
    have parts := of_decide_eq_true edge
    apply decide_eq_true
    rcases parts with forward | backward
    · exact Or.inr ⟨forward.2, forward.1⟩
    · exact Or.inl ⟨backward.2, backward.1⟩
  bidirected_irreflexive := by
    intro node
    apply decide_eq_false
    intro edge
    rcases edge with forward | backward <;> omega

private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if equal : SeparationNode.beq left right = true then isTrue ((SeparationNode.beq_eq_true_iff left right).mp equal)
  else isFalse (fun same => equal ((SeparationNode.beq_eq_true_iff left right).mpr same))

def cut : GraphMutilation signature := .none signature

def actualPath : ActivePath graph cut NodeSet.empty (.observed source) (.observed outcome) where
  nodes := [.observed source, .observed fork, .observed middle, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inr ?_, Or.inl ?_, Or.inl ?_, True.intro⟩ <;> decide +kernel
  source_open := rfl
  target_open := rfl
  internal_active := .step
    (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), rfl⟩)
    (.step (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), rfl⟩)
      (.pair (.observed middle) (.observed outcome)))

def constructedSignal : LinearSignal graph := .ofActivePath actualPath
def heads : NodeSet signature := ActivePathInput.headRows graph cut actualPath.nodes
def endpoints : NodeSet signature := NodeSet.union (NodeSet.singleton source) (NodeSet.singleton outcome)

/-- The fork is really on the path, but its row must not be selected. -/
theorem fork_is_not_a_head : .observed fork ∈ actualPath.nodes ∧ heads fork = false ∧
    heads source = true ∧ heads middle = true ∧ heads outcome = true := by decide +kernel

/-- A declared shortcut is available in the original graph but not read
by the actual path's installed local signal. -/
theorem off_path_parent_not_read : signature.directed fork outcome = true ∧
    constructedSignal.parentMask outcome fork = false := by decide +kernel

/-- The original graph has a genuine reserved root; no latent occurrence
of it lies on this observed-only path, so all its masks remain false. -/
theorem unused_reserved_input (child : Fin signature.count) (root : Fin (pairRootCount graph.binary)) :
    ActivePathInput.pairUsed graph actualPath.nodes root = false ∧ constructedSignal.rootMask child root = false := by
  decide +kernel +revert

theorem all_original_roots_cancel (root : Fin (pairRootCount graph.binary)) :
    constructedSignal.forestRootCoefficient heads root = false :=
  LinearSignal.ofActivePath_forestRootCoefficient actualPath root

theorem actual_observed_boundary (child : Fin signature.count) :
    ActivePathInput.observedBoundary graph cut actualPath.nodes child = endpoints child := by
  decide +kernel +revert

/-- Every actual cube point satisfies endpoint conservation.  Selecting
the fork's own row would add its uncancelled bit, so heads are essential. -/
theorem actual_complete_phase (point : Cube graph) :
    (constructedSignal.forestPhase heads).value point = (maskPhase _ (cubeMask graph endpoints)).value point := by
  change ((LinearSignal.ofActivePath actualPath).forestPhase (ActivePathInput.headRows _ _ _)).value point = _
  rw [LinearSignal.ofActivePath_forestPhase]
  exact congrArg (fun mask => (maskPhase _ (cubeMask graph mask)).value point) (funext actual_observed_boundary)

def direction : Cube graph := joinCube graph (fun _ => false) (fun child => decide (child ≠ source))

theorem actual_direction_rows : (constructedSignal.rowPhase source).value direction = true ∧
    (constructedSignal.rowPhase middle).value direction = false ∧
    (constructedSignal.rowPhase outcome).value direction = false ∧
    (constructedSignal.rowPhase fork).value direction = true := by decide +kernel

/-- Incoming-cut heads are excluded even when the same stored list is
inspected as raw data; no path certificate for a removed edge is invented. -/
theorem cut_head_not_selected :
    ActivePathInput.headRows graph (.bar (NodeSet.singleton outcome)) actualPath.nodes outcome = false := by
  decide +kernel

end ObservedFork
end CurrentHedgeChannelPathInputs
end Examples
end Causality
end Thesis
