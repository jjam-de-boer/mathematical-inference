import Thesis.CausalTransport.ConditionalFailureCoreIncidence
import Thesis.Examples.ConditionalFailureActivationSelection
import Thesis.Examples.ConditionalFailureFlowBoundary
import Thesis.Examples.ConditionalFailureSmallPrefixDirection

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailureCoreIncidence

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation

/-!
# Core column theorems on genuine numerator hedges and actual hard boundaries

The first client reuses the genuine five-vertex collider hedge with Small
`C,Z,P`.  Its common complete activation traces lie inside Small, so the new
column proofs must permit Small/core overlap.  The actual conditioned-boundary
certificate and opaque constructed normal form are reused literally.  The
tests do not evaluate normalization search or substitute the displayed path.
Every actually retained transmitting trace has the two proved installed row
values and original-cylinder support, and both rows remain in the full union.
All original root entries are checked through the exact original incidence
formula, whether or not the opaque normal form uses a particular root.

The second client is the genuine outside-Small-pivot hedge with Small `U,R`
and normalized path `P <- Y`.  Its original graph has two independent pair
roots, but that particular normalized path uses neither.  The universal root
column theorem proves that neither root is read by any installed row; this
is stronger than conservation of two arbitrary, canceling root reads.  Both
original coordinates nevertheless remain free on the evidence cylinder.

These clients check application to actual failed-query graph data.  The
universal trace/root theorems, not fixture-specific phase decisions, supply
their conclusions.  They do not assert the remaining global incidence route
or universal conditional completeness.
-/

namespace SmallOverlap

open CurrentConditionalFailureActivationSelection

abbrev retainedPivot : RetainedConditionalPivot query := pivot.toRetained
abbrev cutForest : ConditionalCutColliderActivationForest query retainedPivot.node := forest.toCutForest
abbrev boundary := CurrentConditionalFailureFlowBoundary.ConditionedCollider.boundary

/-- The complete real all-Small installation permits the actual trace
union inside Small.  No second background copy of those rows is introduced. -/
def installed : LinearSignal graph := normal.forkAbsorbedInteractionSignal boundary retainedPivot cutForest

/-- At every genuine transmitting trace coordinate, all actual row
values are the own/successor pair supplied by the universal theorem. -/
theorem actual_trace_basis_pair {parent next : Fin signature.count}
    (selected : normal.activationTraceNodes retainedPivot cutForest parent = true)
    (edge : normal.activationTraceSuccessor retainedPivot cutForest parent = some next)
    (row : Fin signature.count) :
    (installed.rowPhase row).value
      (basisAssignment (pairRootCount graph.binary + signature.count) (Fin.natAdd (pairRootCount graph.binary) parent)) =
      Bool.xor (decide (row = parent)) (decide (row = next)) :=
  normal.activationTrace_basis_pair boundary retainedPivot cutForest selected edge row

/-- The same actual basis fixes every original action and conditioner;
support is not inferred just from a fixture's singleton evidence assignment. -/
theorem actual_trace_basis_supported {parent next : Fin signature.count}
    (selected : normal.activationTraceNodes retainedPivot cutForest parent = true)
    (edge : normal.activationTraceSuccessor retainedPivot cutForest parent = some next) :
    basisAssignment (pairRootCount graph.binary + signature.count) (Fin.natAdd (pairRootCount graph.binary) parent) ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) :=
  normal.activationTrace_basis_supported retainedPivot cutForest selected edge

/-- A trace pair remains present even when its source row is already
mandatory Small.  The own bit is installed once, not duplicated by overlap. -/
theorem actual_trace_rows_retained {parent next : Fin signature.count}
    (selected : normal.activationTraceNodes retainedPivot cutForest parent = true)
    (edge : normal.activationTraceSuccessor retainedPivot cutForest parent = some next) :
    witness.small parent = true ∧
      normal.forkAbsorbedInteractionRows boundary retainedPivot cutForest parent = true ∧
      normal.forkAbsorbedInteractionRows boundary retainedPivot cutForest next = true :=
  ⟨normal_trace_union_inside_small parent selected,
    normal.activationTrace_pair_rows_selected boundary retainedPivot cutForest selected edge⟩

/-- Every original root entry comes from the opaque actual path's
occurrence test and its real local incidence, with no global switching input. -/
theorem actual_root_columns (root : Fin (pairRootCount graph.binary)) (row : Fin signature.count) :
    installed.rootRowCoefficient row root =
      (ActivePathInput.pairUsed graph normal.cutPath.nodes root && pairRootIncident graph.binary root row) :=
  normal.forkAbsorbedInteraction_root_coefficient boundary retainedPivot cutForest row root

end SmallOverlap

namespace OutsideSmallPivot

open CurrentConditionalFailureSmallPrefixDirection

/-- The displayed window is a theorem about the actual opaque normal
form.  Its absence of latent vertices rejects both original root occurrences. -/
theorem actual_roots_unused (root : Fin (pairRootCount graph.binary)) :
    ActivePathInput.pairUsed graph normal.cutPath.nodes root = false := by
  rw [normal_window]
  apply Bool.eq_false_iff.mpr
  intro used
  rcases (ActivePathInput.pairUsed_eq_true_iff graph _ root).mp used with member | member <;>
    simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member

/-- No installed row reads either unused original root.  The proof uses
the universal actual-column identity, not a complete-cube parity calculation. -/
theorem unused_root_basis_zero (root : Fin (pairRootCount graph.binary)) (row : Fin signature.count) :
    ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
      (basisAssignment (pairRootCount graph.binary + signature.count) (root.castAdd signature.count)) = false := by
  rw [LinearSignal.rowPhase_root_basis,
    normal.forkAbsorbedInteraction_root_coefficient boundary pivot forest row root,
    actual_roots_unused root, Bool.false_and]

/-- Those unused original roots are still retained independent inputs,
not removed from the unchanged original graph or its conditioning cylinder. -/
theorem original_root_basis_supported (root : Fin (pairRootCount graph.binary)) :
    basisAssignment (pairRootCount graph.binary + signature.count) (root.castAdd signature.count) ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) :=
  ConditionalBackdoorPathNormalForm.originalRoot_basis_supported root

end OutsideSmallPivot

end CurrentConditionalFailureCoreIncidence
end Examples
end Causality
end Thesis
