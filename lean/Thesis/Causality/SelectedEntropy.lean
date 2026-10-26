import Thesis.Causality.SelectedAssignment
import Thesis.Probability.Distros.Entropy

namespace Thesis
namespace Causality

open Probability Probability.Distros

variable {S : ObservedSignature}

/-!
# Entropy of selected observed coordinates

Shannon entropy of a finite assignment law is computed on the signature's
duplicate-free assignment enumeration.  Selected-coordinate entropy pushes
the law through the existing canonical projection: unselected coordinates
are replaced by defaults, so repeated full assignments that agree on the
selected set become one observable cell.

These definitions apply to any finite assignment record, observational or
interventional.  They do not assume that an observed-parent factorization
survives hidden-variable marginalisation, and they do not treat a single
node entropy as a sufficient statistic for a joint.
-/

/-- Duplicate-free grid of every dependent observed assignment. -/
def ObservedSignature.assignmentGrid (S : ObservedSignature) : EntropyGrid S.Assignment :=
  ⟨S.assignmentEnumeration, S.assignmentEnumeration_nodup⟩

def assignmentSupport (μ : Distro S.Assignment) :
    μ.AlmostSurely (fun assignment => assignment ∈ S.assignmentEnumeration) := by
  intro atom _ _
  exact S.assignmentEnumeration_complete atom.1

/-- Joint Shannon entropy of a finite observed assignment law. -/
def jointEntropy (μ : Distro S.Assignment) : ExactLog :=
  μ.entropy S.assignmentGrid (assignmentSupport μ)

/-- Duplicate-free grid of canonical selected-coordinate presentations. -/
def ObservedSignature.selectedGrid (S : ObservedSignature) (nodes : NodeSet S) :
    EntropyGrid (S.SelectedAssignment nodes) :=
  ⟨S.selectedAssignmentEnumeration nodes, S.selectedAssignmentEnumeration_nodup nodes⟩

def selectedSupport (μ : Distro S.Assignment) (nodes : NodeSet S) :
    (μ.map (S.selectAssignment nodes)).AlmostSurely
      (fun assignment => assignment ∈ S.selectedAssignmentEnumeration nodes) := by
  intro atom _ _
  exact S.selectedAssignmentEnumeration_complete nodes atom.1

/-- Entropy of the selected coordinates of an assignment law. -/
def selectedEntropy (μ : Distro S.Assignment) (nodes : NodeSet S) : ExactLog :=
  (μ.map (S.selectAssignment nodes)).entropy (S.selectedGrid nodes) (selectedSupport μ nodes)

/-- Law agreement transports joint entropy.  Entropy is a functional of the
entire assignment law, not of a single event probability. -/
theorem jointEntropy_sameLaw {μ ν : Distro S.Assignment} (same : μ.SameLaw ν) :
    ExactLog.Equiv (jointEntropy μ) (jointEntropy ν) :=
  Distro.entropy_sameLaw same S.assignmentGrid (assignmentSupport μ) (assignmentSupport ν)

theorem selectedEntropy_sameLaw {μ ν : Distro S.Assignment} (same : μ.SameLaw ν)
    (nodes : NodeSet S) :
    ExactLog.Equiv (selectedEntropy μ nodes) (selectedEntropy ν nodes) :=
  Distro.entropy_sameLaw (Distro.SameLaw.map same (S.selectAssignment nodes))
    (S.selectedGrid nodes) (selectedSupport μ nodes) (selectedSupport ν nodes)

end Causality
end Thesis
