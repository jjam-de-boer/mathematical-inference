import Thesis.CausalTransport.ConditionalFailurePathDirection
import Thesis.Examples.HedgeChannelPathRows
import Thesis.Examples.ConditionalFailurePathNormalization

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentHedgeChannelPathDirection

open PathSpecification Probability FiniteBooleanInteraction
open HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# General supported directions on real observed and original-root paths

These fixtures now use the general direction constructor and its proved
support/parity theorems, not supplied hand-written parity certificates.  The
actual path inputs remain the installed guarded inputs from earlier tests.

The reversed-pair chain tests one original shared root and an incoming
observed target.  The observed fork tests omission of its odd own row,
even though an unused original reserved coordinate is now true.  The mixed
conditioned collider tests an outgoing target whose odd own row is omitted.
The two-root collider matches the earlier literal control direction while
retaining two distinct original input coordinates.

Finally the real normalized exchange constructor supplies the full original
query's support, its first incoming edge, and selected parities without an
independent orientation flag.  That observationally identifiable fixture
still has no joint hedge and is not advertised as a conditional countermodel.
-/

namespace ReversedPair

open CurrentActivePathPairRoots

/-- The general theorem identifies the selected-row parity function on
this genuine reversed-label path.  No parity is checked by cube enumeration. -/
theorem general_selected_rows (child : Fin signature.count) :
    (if ActivePathInput.headRows graph cut actualPath.nodes child then
      ((LinearSignal.ofActivePath actualPath).rowPhase child).value (LinearSignal.activePathDirection actualPath) else false) =
        decide (child = leftNode) :=
  LinearSignal.activePathDirection_selected_row actualPath reversedPair [.observed rightNode, .observed outcome]
    rfl (by decide +kernel) child

/-- The actual complete head interaction is odd by the general theorem,
including all of its original reserved and observed row coordinates. -/
theorem general_head_phase_odd :
    ((LinearSignal.ofActivePath actualPath).forestPhase (ActivePathInput.headRows graph cut actualPath.nodes)).value
      (LinearSignal.activePathDirection actualPath) = true :=
  LinearSignal.activePathDirection_forest_odd actualPath reversedPair [.observed rightNode, .observed outcome]
    rfl (by decide +kernel)

end ReversedPair

namespace ObservedFork

open CurrentHedgeChannelPathInputs.ObservedFork

/-- The fork does not become a selected head merely because its direction
bit is true.  The general row theorem keeps it out of the parity function. -/
theorem general_selected_rows (child : Fin signature.count) :
    (if heads child then (constructedSignal.rowPhase child).value (LinearSignal.activePathDirection actualPath) else false) =
      decide (child = source) :=
  LinearSignal.activePathDirection_selected_row actualPath (.observed fork) [.observed middle, .observed outcome]
    rfl (by decide +kernel) child

/-- Every original reserved bit may be true in this supported direction.
The unused bit is nevertheless unread by every actual installed row. -/
theorem unused_true_root_not_read (child : Fin signature.count) (root : Fin (pairRootCount graph.binary)) :
    cubeEnvironment graph (LinearSignal.activePathDirection actualPath) root = true ∧
      constructedSignal.rootMask child root = false :=
  ⟨LinearSignal.activePathDirection_environment actualPath root, (unused_reserved_input child root).2⟩

/-- The omitted fork's actual row really is odd in the general direction.
This guards against replacing selected-head evenness by all-row evenness. -/
theorem omitted_fork_is_odd :
    (constructedSignal.rowPhase fork).value (LinearSignal.activePathDirection actualPath) = true := by
  change ((LinearSignal.ofActivePath actualPath).rowPhase fork).value (LinearSignal.activePathDirection actualPath) = true
  rw [LinearSignal.ofActivePath_rowPhase_of_not_head actualPath fork (by decide +kernel),
    LinearSignal.activePathDirection_sample]
  rfl

end ObservedFork

namespace ConditionedCollider

open CurrentActivePathBoundary.ConditionedCollider

/-- Conditioning support includes both the real collider and the source,
while all original reserved bits remain free on the same complete cylinder. -/
theorem general_direction_supported :
    LinearSignal.activePathDirection actualPath ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union given (NodeSet.singleton pivot))) :=
  LinearSignal.activePathDirection_member actualPath

/-- The mixed incoming collider row is even by the general selected-row
theorem.  The outgoing endpoint has no selected-row parity contribution. -/
theorem general_selected_rows (child : Fin signature.count) :
    (if heads child then (signalData.rowPhase child).value (LinearSignal.activePathDirection actualPath) else false) =
      decide (child = pivot) :=
  LinearSignal.activePathDirection_selected_row actualPath reversedPair [.observed collider, .observed outcome]
    rfl (by decide +kernel) child

/-- The outgoing outcome's own row is odd but is correctly omitted.
Its true direction bit still supplies the actual collider's observed input. -/
theorem omitted_outcome_is_odd :
    (signalData.rowPhase outcome).value (LinearSignal.activePathDirection actualPath) = true := by
  change ((LinearSignal.ofActivePath actualPath).rowPhase outcome).value (LinearSignal.activePathDirection actualPath) = true
  rw [LinearSignal.ofActivePath_rowPhase_of_not_head actualPath outcome (by decide +kernel),
    LinearSignal.activePathDirection_sample]
  rfl

end ConditionedCollider

namespace DoubleLatentCollider

open CurrentHedgeChannelPathRows.DoubleLatentCollider

/-- The general constructor recovers the earlier explicitly displayed
direction at every original coordinate, not at a renamed common switch. -/
theorem general_direction_matches_control : LinearSignal.activePathDirection actualPath = direction := by
  funext coordinate
  decide +kernel +revert

/-- Both real latent neighbours are handled by the same general theorem.
The collider's two distinct reserved reads cancel in the direction; the
source is the only odd selected head. -/
theorem general_selected_rows (child : Fin signature.count) :
    (if heads child then (signalData.rowPhase child).value (LinearSignal.activePathDirection actualPath) else false) =
      decide (child = pivot) :=
  LinearSignal.activePathDirection_selected_row actualPath firstPair [.observed collider, secondPair, .observed outcome]
    rfl (by decide +kernel) child

end DoubleLatentCollider

namespace NormalizedExchange

open CurrentConditionalFailurePathNormalization

/-- The actual normalized exchange data supply original-query support,
including the retained conditioner, without a separate support premise. -/
theorem original_query_support :
    normal.pathDirection ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) := normal.pathDirection_member

/-- The graph adapter derives the first incoming edge from the exact cut,
then proves pivot oddness and its head membership.  Only the actual query's
retained-conditioner certificate is supplied. -/
theorem normalized_source_odd :
    ActivePathInput.headRows graph (GraphMutilation.barUnderline query.action (NodeSet.singleton conditioner)) normal.cutPath.nodes conditioner = true ∧
      ((LinearSignal.ofActivePath normal.cutPath).rowPhase conditioner).value normal.pathDirection = true :=
  normal.pathDirection_source_odd (by decide +kernel)

/-- Every other actual head of this normalized signal is even through the
general proof, rather than a finite decision of its local row expression. -/
theorem normalized_selected_even (child : Fin signature.count)
    (head : ActivePathInput.headRows graph (GraphMutilation.barUnderline query.action (NodeSet.singleton conditioner)) normal.cutPath.nodes child = true)
    (different : child ≠ conditioner) :
    ((LinearSignal.ofActivePath normal.cutPath).rowPhase child).value normal.pathDirection = false :=
  normal.pathDirection_selected_even (by decide +kernel) child head different

/-- Both the selected outcome bit and the entire normalized path-head
interaction are odd.  Neither conclusion establishes a mandatory Small
forest, which is deliberately absent from this identifiable fixture. -/
theorem normalized_complete_parity : cubeSample graph normal.pathDirection normal.outcome = true ∧
    ((LinearSignal.ofActivePath normal.cutPath).forestPhase
      (ActivePathInput.headRows graph (GraphMutilation.barUnderline query.action (NodeSet.singleton conditioner)) normal.cutPath.nodes)).value
        normal.pathDirection = true :=
  ⟨normal.pathDirection_outcome_bit (by decide +kernel), normal.pathDirection_forest_odd (by decide +kernel)⟩

end NormalizedExchange
end CurrentHedgeChannelPathDirection
end Examples
end Causality
end Thesis
