import Thesis.CausalTransport.ActivePathForkOrientation
import Thesis.CausalTransport.HedgeChannelPathDirection

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentActivePathForkOrientation

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# Source-side cancellation must not follow observed vertex numbering

The four three-valued vertices are `U,Y,C,P`, in that numbered order.  Actual
arrows are `U -> P`, `U,Y -> C`; the path is `P <- U -> C <- Y`, with collider
`C` directly conditioned.  The source-side head `P` has index 3, while the
outcome-side head `C` has index 2.  An ascending signature scan would therefore
choose `U -> C`, canceling the wrong side for the intended outcome connection.

The actual path-order scan chooses `U -> P`, as the general internal-window
theorem predicts.  Absorption cancels that read, retains `C`'s original `U`
input, and keeps the whole original-input phase.  At the unchanged supported
path direction the newly retained `U` row is uniquely odd; both original
heads are even.  In contrast the former numbered choice leaves both original
heads odd at that same direction, despite remaining a legal outgoing edge.

This is an actual active-path/signal regression, not a supplied hedge or a
claim of conditional nonidentifiability.  Its purpose is to distinguish a
proved source-side orientation from mere edge legality and conservation.
-/

def signature : ObservedSignature where
  count := 4
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => (by decide : (List.finRange 3).Nodup)
  defaultValue := fun _ => ⟨0, by decide⟩
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide
    ((parent.val = 0 ∧ (child.val = 2 ∨ child.val = 3)) ∨ (parent.val = 1 ∧ child.val = 2))
  directed_earlier := by intro parent child edge; have parts := of_decide_eq_true edge; omega

def parent : Fin signature.count := ⟨0, by decide⟩
def outcome : Fin signature.count := ⟨1, by decide⟩
def collider : Fin signature.count := ⟨2, by decide⟩
def pivotNode : Fin signature.count := ⟨3, by decide⟩

def graph : ObservedGraph signature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ edge; cases edge
  bidirected_irreflexive := fun _ => rfl

private instance : DecidableEq (SeparationNode signature) := fun left right =>
  if same : SeparationNode.beq left right = true then isTrue ((SeparationNode.beq_eq_true_iff left right).mp same)
  else isFalse (fun equal => same ((SeparationNode.beq_eq_true_iff left right).mpr equal))

def cut : GraphMutilation signature := .barUnderline NodeSet.empty (NodeSet.singleton pivotNode)
def given : NodeSet signature := NodeSet.singleton collider

/-- The displayed real path is active in the singleton outgoing cut;
the collider is itself conditioned, with no invented activating suffix. -/
def path : ActivePath graph cut given (.observed pivotNode) (.observed outcome) where
  nodes := [.observed pivotNode, .observed parent, .observed collider, .observed outcome]
  starts := rfl
  finishes := rfl
  simple := by decide +kernel
  adjacent := by refine ⟨Or.inr ?_, Or.inl ?_, Or.inr ?_, True.intro⟩ <;> decide +kernel
  source_open := by decide +kernel
  target_open := by decide +kernel
  internal_active := .step
    (Or.inr ⟨graph.not_collider_of_outgoing cut (by decide +kernel), by unfold NonColliderOpen; decide +kernel⟩)
    (.step (Or.inl ⟨⟨by decide +kernel, by decide +kernel⟩,
      graph.ancestorOf_target cut given (target := collider) (by decide +kernel)⟩)
      (.pair (.observed collider) (.observed outcome)))

private theorem distinct : pivotNode ≠ outcome := by decide +kernel
private theorem actual_fork : path.forkNodes parent = true := by decide +kernel

def selected : NodeSet signature := NodeSet.singleton parent
def successor : ForestChild signature := path.forkRoutingSuccessor distinct selected
def heads : NodeSet signature := ActivePathInput.headRows graph cut path.nodes
def rows : NodeSet signature := NodeSet.union heads (path.forkRoutingNodes selected)
def installed : LinearSignal graph := (LinearSignal.ofActivePath path).absorbSuccessor heads successor
def direction : Cube graph := LinearSignal.activePathDirection path

/-- Numbering really prefers `C`, so the path-order result below cannot
be a coincidental reuse of the old ascending signature scan. -/
theorem numbered_scan_wrong_side : collider.val < pivotNode.val ∧
    (NodeSet.enumerated signature).find?
      (fun child => ActivePathInput.incomingEdge graph cut path.nodes (.observed parent) child) = some collider := by
  decide +kernel

/-- The general theorem, not a literal edge flag, chooses preceding `P`. -/
theorem path_order_source_side : successor parent = some pivotNode := by
  unfold successor PathSpecification.ActivePath.forkRoutingSuccessor
  rw [restrictChild_of_true (by decide +kernel : path.forkRoutingNodes selected parent = true)]
  exact path.forkSuccessor_internal_window distinct parent pivotNode collider [] [.observed outcome] rfl actual_fork

theorem source_side_canceled : installed.parentMask pivotNode parent = false :=
  path.forkRouting_cancels_chosen_input distinct selected path_order_source_side

theorem outcome_side_retained : installed.parentMask collider parent = true := by
  decide +kernel

/-- Source-side cancellation preserves every original cube point before
any conditioning or inspection of the supported direction. -/
theorem whole_cube_conservation (point : Cube graph) :
    (installed.forestPhase rows).value point = ((LinearSignal.ofActivePath path).forestPhase heads).value point :=
  path.forkRouting_preserves_phase distinct selected point

/-- The actual direction fixes both original conditioners, not just the
exchange-test given set which omitted the pivot. -/
theorem direction_supported : direction ∈
    FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union given (NodeSet.singleton pivotNode))) :=
  LinearSignal.activePathDirection_member path

theorem outcome_odd : (maskPhase _ (cubeMask graph (NodeSet.singleton outcome))).value direction = true := by
  decide +kernel

theorem retained_fork_unique_odd : (installed.rowPhase parent).value direction = true ∧
    (forall child, rows child = true -> child ≠ parent -> (installed.rowPhase child).value direction = false) := by
  decide +kernel

/-- The old numbered exit is still a real local arrow; its failure below
is about parity orientation, not access to an unavailable input. -/
def numberedSuccessor : ForestChild signature := fun node => if node = parent then some collider else none
def numberedInstalled : LinearSignal graph := (LinearSignal.ofActivePath path).absorbSuccessor heads numberedSuccessor

theorem numbered_exit_legal : childWellFormedBool rows numberedSuccessor = true := by decide +kernel

/-- Both outside original heads stay odd under the wrongly oriented legal
exit at the same supported direction.  Legality alone did not give balance. -/
theorem numbered_exit_background_odd : (numberedInstalled.rowPhase pivotNode).value direction = true ∧
    (numberedInstalled.rowPhase collider).value direction = true := by
  decide +kernel

end CurrentActivePathForkOrientation
end Examples
end Causality
end Thesis
