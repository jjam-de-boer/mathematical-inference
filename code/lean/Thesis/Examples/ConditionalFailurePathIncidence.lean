import Thesis.CausalTransport.ConditionalFailurePathIncidence
import Thesis.Examples.ConditionalFailureSmallPrefixDirection

namespace Thesis
namespace Causality
namespace Examples
namespace CurrentConditionalFailurePathIncidence

open PathSpecification Probability FiniteBooleanInteraction
  HedgeChannelInstallation HedgeChannelEnvironmentInstallation
open CurrentConditionalFailureSmallPrefixDirection

/-!
# The actual outcome column starts at the outside-Small pivot's real row

The existing genuine five-vertex failure has Small `U,R`, conditioner `P`
outside Small, and opaque constructed normal path `P <- Y`.  Its outcome
endpoint `Y` is outgoing and is not selected as a path head.  The real
all-Small conditioned boundary avoids every original outcome, so the
complete installed row union does not add `Y` as a mandatory prefix row.

The unified outcome theorem nevertheless supplies one selected-row incidence
for the actual supported `Y` coordinate.  Its receiving head is the real
`P` row.  Here that identification uses the already proved singleton core,
not evaluation of the opaque normalization search or a supplied endpoint
orientation flag.  The complete selected-row test includes intermediate
Small rows and the original pivot outside Small; none is omitted.

This is the starting column for a subsequent global incidence connection.
The companion already constructs this fixture's countermodels.  The test
does not replace the remaining universal outcome-to-Small reachability and
supported even-background direction theorem by this one successful instance.
-/

/-- Every original queried outcome is absent from these actual stopped
Small-source prefixes, and outgoing `Y` has no row in the installed union. -/
theorem actual_outcome_unselected : normal.forkAbsorbedInteractionRows boundary pivot forest normal.outcome = false := by
  apply normal.pathOutcome_nonhead_rows_free boundary pivot forest
  have same := (NodeSet.singleton_eq_true_iff outcome normal.outcome).mp normal.outcome_selected
  rw [same]
  unfold ConditionalBackdoorPathNormalForm.pathHeads
  rw [normal_window]
  decide +kernel

/-- The general endpoint theorem yields exactly the retained `P` row
incidence on the complete selected-row union.  The original outcome bit
itself is not installed as an extra mechanism or global switching input. -/
theorem actual_outcome_basis_pivot (row : Fin signature.count) :
    (if normal.forkAbsorbedInteractionRows boundary pivot forest row then
      ((normal.forkAbsorbedInteractionSignal boundary pivot forest).rowPhase row).value
        (basisAssignment (pairRootCount graph.binary + signature.count) (Fin.natAdd (pairRootCount graph.binary) normal.outcome))
      else false) = decide (row = pivotNode) := by
  rcases normal.pathOutcome_selected_basis_single boundary pivot forest with ⟨receiver, head, _selected, column⟩
  have core : normal.smallInteractionRows pivot forest receiver = true :=
    NodeSet.subset_union_left _ _ receiver (NodeSet.subset_union_left _ _ receiver head)
  rw [actual_core] at core
  have same := (NodeSet.singleton_eq_true_iff pivotNode receiver).mp core
  rw [same] at column
  exact column row

/-- This is support for the full unchanged action/condition cylinder,
including the pivot omitted from the exchange test's temporary given set. -/
theorem actual_outcome_basis_supported :
    basisAssignment (pairRootCount graph.binary + signature.count) (Fin.natAdd (pairRootCount graph.binary) normal.outcome) ∈
      FiniteProduct.falseCylinderEnumeration (pairRootCount graph.binary + signature.count)
        (cubeMask graph (NodeSet.union query.action query.condition)) :=
  normal.pathOutcome_basis_supported pivot

end CurrentConditionalFailurePathIncidence
end Examples
end Causality
end Thesis
