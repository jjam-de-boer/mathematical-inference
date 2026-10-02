import Thesis.Causality.Model

namespace Thesis
namespace Causality

open Probability

/-!
# Explicit finite assignments on a selected coordinate set

A conditional probability table needs one row per outcome assignment and
one column per conditioning assignment.  Enumerating full assignments and
forgetting unselected coordinates would repeat each row many times.

`SelectedAssignment` instead uses the existing canonical projection: values
off the selected set are the signature's supplied defaults.  Its enumeration
maps the complete observed enumeration through that projection, then removes
duplicates constructively.  No representative is chosen from an equivalence
class or from a proposition.  Empty selections have their canonical default
assignment, and nonbinary dependent coordinate types are retained literally.
-/

namespace ObservedSignature

/-- A full assignment whose unselected coordinates are canonical defaults.
The subtype proof records the projection invariant, not additional data
chosen from an existential statement. -/
def SelectedAssignment (S : ObservedSignature) (nodes : NodeSet S) :=
  {assignment : S.Assignment // S.project nodes assignment = assignment}

instance (S : ObservedSignature) (nodes : NodeSet S) : DecidableEq (S.SelectedAssignment nodes) :=
  inferInstanceAs (DecidableEq {assignment : S.Assignment // S.project nodes assignment = assignment})

/-- The canonical selected-coordinate presentation of a supplied assignment. -/
def selectAssignment (S : ObservedSignature) (nodes : NodeSet S) (assignment : S.Assignment) :
    S.SelectedAssignment nodes := ⟨S.project nodes assignment, S.project_idempotent nodes assignment⟩

/-- Finite, duplicate-free selected assignments computed from existing
signature data.  Every selected value is reached by projecting itself. -/
def selectedAssignmentEnumeration (S : ObservedSignature) (nodes : NodeSet S) : List (S.SelectedAssignment nodes) :=
  deduplicate (S.assignmentEnumeration.map (S.selectAssignment nodes))

theorem selectedAssignmentEnumeration_complete (S : ObservedSignature) (nodes : NodeSet S)
    (assignment : S.SelectedAssignment nodes) : assignment ∈ S.selectedAssignmentEnumeration nodes := by
  apply (mem_deduplicate _ _).mpr
  apply List.mem_map.mpr
  refine ⟨assignment.val, S.assignmentEnumeration_complete assignment.val, ?_⟩
  exact Subtype.ext assignment.property

theorem selectedAssignmentEnumeration_nodup (S : ObservedSignature) (nodes : NodeSet S) :
    (S.selectedAssignmentEnumeration nodes).Nodup := deduplicate_nodup _

end ObservedSignature

end Causality
end Thesis
