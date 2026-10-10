import Thesis.CausalTransport.ConditionalFailurePathNormalization
import Thesis.CausalTransport.HedgeChannelPathDirection

namespace Thesis
namespace Causality

open PathSpecification Probability FiniteBooleanInteraction
open HedgeChannelEnvironmentInstallation

/-!
# The normalized exchange path supplies its actual supported odd direction

The general incoming-path direction now applies to the normalized path in
the exact singleton exchange graph.  Its first incoming arrow is derived
from that graph's outgoing cut and the actual list decoder, not supplied
as another readiness premise.  Outcome/condition disjointness proves that
the two endpoints differ.

The direction is supported on the *original* action-plus-condition cylinder,
including the pivot removed from the exchange test's conditioning set.
It fixes that pivot to false explicitly, and activity fixes every other
conditioned coordinate.  Individual selected-row parities and oddness of
the complete path-head interaction follow from the general theorems.

No joint hedge is assumed or constructed here.  Exhausted exchange alone
can occur in an observationally identifiable query.  The direction is real
graph-to-signal data, not a conditional countermodel.  The separate
`ConditionalFailureActivationInteraction` installs the actual activation
traces; the entire mandatory Small forest and any required Small-to-pivot
oddness transfer still have to be assembled before conditional completeness.
-/

variable {S : ObservedSignature.{0}} {graph : ObservedGraph S}
  {query : ConditionalKernelQuery S} {node : Fin S.count}

namespace ConditionalBackdoorPathNormalForm

/-- The same original-input cube direction built from this normalized
cut path.  Its collider mask is exactly the path classifier also used by
the normalized activation selection, not a separate proposed partition. -/
def pathDirection (normal : ConditionalBackdoorPathNormalForm graph query node) : Cube graph :=
  LinearSignal.activePathDirection normal.cutPath

private theorem cut_source_outgoing_false (next : SeparationNode S) :
    graph.expandedMutilatedEdge (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
      (.observed node) next = false := by
  have self := (NodeSet.singleton_eq_true_iff node node).mpr rfl
  cases next with
  | observed child =>
      simp only [ObservedGraph.expandedMutilatedEdge, GraphMutilation.barUnderline,
        self, Bool.not_true, Bool.and_false, Bool.false_and]
  | latentPair _ _ => rfl

private theorem cut_first_incoming (normal : ConditionalBackdoorPathNormalForm graph query node)
    (selected : query.condition node = true) :
    graph.expandedMutilatedEdge (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
      (normal.backdoor selected).first (.observed node) = true := by
  have consecutive := normal.cutPath.adjacent
  have shape : normal.cutPath.nodes = .observed node :: (normal.backdoor selected).first :: (normal.backdoor selected).rest :=
    (normal.backdoor selected).nodes_eq
  rw [shape] at consecutive
  rcases consecutive.1 with outgoing | incoming
  · rw [cut_source_outgoing_false] at outgoing
    cases outgoing
  · exact incoming

private theorem endpoints_distinct (normal : ConditionalBackdoorPathNormalForm graph query node)
    (selected : query.condition node = true) : node ≠ normal.outcome := by
  intro equal
  have free := query.outcome_condition_disjoint normal.outcome normal.outcome_selected
  exact Bool.false_ne_true (free.symm.trans (equal ▸ selected))

/-- The observed direction is false on the complete original action and
condition selection, including the pivot whose singleton exchange test
temporarily removed it.  No zero-evidence assumption is added to the query. -/
theorem pathDirection_fixed (normal : ConditionalBackdoorPathNormalForm graph query node)
    (child : Fin S.count) (fixed : NodeSet.union query.action query.condition child = true) :
    cubeSample graph normal.pathDirection child = false := by
  rw [pathDirection, LinearSignal.activePathDirection_sample]
  by_cases atSource : child = node
  · subst child
    exact ActivePathInput.nonColliderBits_source _ _ _ _
  · apply ActivePathInput.nonColliderBits_condition_false normal.cutPath child
    rcases Bool.or_eq_true_iff.mp fixed with action | condition
    · exact Bool.or_eq_true_iff.mpr (Or.inl action)
    · have absent : NodeSet.singleton node child = false := by
        apply Bool.eq_false_iff.mpr
        intro same
        exact atSource ((NodeSet.singleton_eq_true_iff node child).mp same)
      apply Bool.or_eq_true_iff.mpr
      apply Or.inr
      change (query.condition child && !(NodeSet.singleton node child)) = true
      rw [condition, absent]
      rfl

/-- Every original reserved coordinate remains free, and all original
fixed observed coordinates are false.  This is the complete conditioning
support needed by the subsequent finite interaction covariance theorem. -/
theorem pathDirection_member (normal : ConditionalBackdoorPathNormalForm graph query node) :
    normal.pathDirection ∈ FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + S.count)
      (cubeMask graph (NodeSet.union query.action query.condition)) := by
  rw [FiniteProduct.BooleanBlocks.cylinder_member_iff]
  simp only [cubeMask, pathDirection, LinearSignal.activePathDirection, joinCube,
    FiniteProduct.BooleanBlocks.leftBlock_join, FiniteProduct.BooleanBlocks.rightBlock_join]
  constructor
  · rw [FiniteProduct.falseCylinderEnumeration_member_iff]
    intro root impossible
    cases impossible
  · rw [FiniteProduct.falseCylinderEnumeration_member_iff]
    intro child fixed
    have zero := normal.pathDirection_fixed child fixed
    rw [pathDirection, LinearSignal.activePathDirection_sample] at zero
    exact zero

/-- The query's selected outcome coordinate is true in the constructed
supported direction.  Its distinction from the fixed pivot is proved from
the actual query's outcome/condition disjointness certificate. -/
theorem pathDirection_outcome_bit (normal : ConditionalBackdoorPathNormalForm graph query node)
    (selected : query.condition node = true) : cubeSample graph normal.pathDirection normal.outcome = true := by
  rw [pathDirection, LinearSignal.activePathDirection_sample]
  exact ActivePathInput.nonColliderBits_target normal.cutPath (endpoints_distinct normal selected)

/-- The exact outgoing-cut normalized path selects the pivot as a head and
leaves its actual row odd.  The first-edge certificate comes from the cut
path itself; no independently supplied orientation or parity flag is used. -/
theorem pathDirection_source_odd (normal : ConditionalBackdoorPathNormalForm graph query node)
    (selected : query.condition node = true) :
    ActivePathInput.headRows graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) normal.cutPath.nodes node = true ∧
      ((LinearSignal.ofActivePath normal.cutPath).rowPhase node).value normal.pathDirection = true :=
  LinearSignal.activePathDirection_source_odd normal.cutPath (normal.backdoor selected).first (normal.backdoor selected).rest
    (normal.backdoor selected).nodes_eq (cut_first_incoming normal selected)

/-- Every other actual selected head is even.  The original query supplies
only that this pivot is a retained conditioner; row evenness is a theorem
of the actual normalized path signal, including its original reserved inputs. -/
theorem pathDirection_selected_even (normal : ConditionalBackdoorPathNormalForm graph query node)
    (selected : query.condition node = true) (child : Fin S.count)
    (head : ActivePathInput.headRows graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) normal.cutPath.nodes child = true)
    (different : child ≠ node) :
    ((LinearSignal.ofActivePath normal.cutPath).rowPhase child).value normal.pathDirection = false :=
  LinearSignal.activePathDirection_selected_even normal.cutPath (normal.backdoor selected).first (normal.backdoor selected).rest
    (normal.backdoor selected).nodes_eq (cut_first_incoming normal selected) child head different

/-- The complete normalized path-head interaction is odd at the supported
direction.  This does not assert oddness of a different mandatory Small
forest when the pivot lies outside that forest. -/
theorem pathDirection_forest_odd (normal : ConditionalBackdoorPathNormalForm graph query node)
    (selected : query.condition node = true) :
    ((LinearSignal.ofActivePath normal.cutPath).forestPhase
      (ActivePathInput.headRows graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) normal.cutPath.nodes)).value
        normal.pathDirection = true :=
  LinearSignal.activePathDirection_forest_odd normal.cutPath (normal.backdoor selected).first (normal.backdoor selected).rest
    (normal.backdoor selected).nodes_eq (cut_first_incoming normal selected)

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
