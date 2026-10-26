import Thesis.Causality.SelectedAssignment
import Thesis.Probability.Distros.EntropyDataProcessing

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

/-- Forgetting a larger selected set onto a subset is the smaller projection. -/
theorem selectAssignment_of_subset {smaller larger : NodeSet S}
    (included : NodeSet.Subset smaller larger) (assignment : S.Assignment) :
    S.selectAssignment smaller assignment =
      S.selectAssignment smaller (S.selectAssignment larger assignment).val := by
  apply Subtype.ext
  exact S.project_subset included assignment

/-- Shannon monotonicity of selected coordinates: a subset cannot have larger
entropy than a superset.  This is data-processing for the canonical projection,
not a causal parent factorization. -/
theorem selectedEntropy_mono (μ : Distro S.Assignment) {smaller larger : NodeSet S}
    (included : NodeSet.Subset smaller larger) :
    ExactLog.LE (selectedEntropy μ smaller) (selectedEntropy μ larger) := by
  let forget : S.SelectedAssignment larger → S.SelectedAssignment smaller :=
    fun assignment => S.selectAssignment smaller assignment.val
  have sameMap :
      (μ.map (S.selectAssignment larger)).map forget =
        μ.map (S.selectAssignment smaller) := by
    rw [Distro.map_comp]
    congr 1
    funext assignment
    exact (selectAssignment_of_subset included assignment).symm
  have targetSupport :
      ((μ.map (S.selectAssignment larger)).map forget).AlmostSurely
        (fun assignment => assignment ∈ S.selectedAssignmentEnumeration smaller) := by
    rw [sameMap]
    exact selectedSupport μ smaller
  have transported :
      ExactLog.Equiv
        (((μ.map (S.selectAssignment larger)).map forget).entropy
          (S.selectedGrid smaller) targetSupport)
        (selectedEntropy μ smaller) :=
    Distro.entropy_sameLaw (by rw [sameMap]; exact Distro.SameLaw.refl _)
      (S.selectedGrid smaller) targetSupport (selectedSupport μ smaller)
  exact (ExactLog.le_congr transported (ExactLog.equiv_refl _)).mp
    (Distro.entropy_map_le (μ.map (S.selectAssignment larger)) forget
      (S.selectedGrid larger) (S.selectedGrid smaller)
      (selectedSupport μ larger) targetSupport
      (S.selectedAssignmentEnumeration_complete larger)
      (S.selectedAssignmentEnumeration_complete smaller))

/-- Conditional entropy of a larger selected set given a subset, as the
grouping remainder of the canonical forgetful map.  This is the full-DAG
chain-rule remainder, not an observed-parent factorization. -/
def selectedConditionalEntropy (μ : Distro S.Assignment)
    (smaller larger : NodeSet S) : ExactLog :=
  let forget : S.SelectedAssignment larger → S.SelectedAssignment smaller :=
    fun assignment => S.selectAssignment smaller assignment.val
  (μ.map (S.selectAssignment larger)).conditionalEntropyMap forget
    (S.selectedGrid larger) (S.selectedGrid smaller)

/-- `H(larger) = H(smaller) + H(larger|smaller)` on selected coordinates. -/
theorem selectedEntropy_chain (μ : Distro S.Assignment) {smaller larger : NodeSet S}
    (included : NodeSet.Subset smaller larger) :
    ExactLog.Equiv (selectedEntropy μ larger)
      (ExactLog.add (selectedEntropy μ smaller)
        (selectedConditionalEntropy μ smaller larger)) := by
  let forget : S.SelectedAssignment larger → S.SelectedAssignment smaller :=
    fun assignment => S.selectAssignment smaller assignment.val
  have sameMap :
      (μ.map (S.selectAssignment larger)).map forget =
        μ.map (S.selectAssignment smaller) := by
    rw [Distro.map_comp]
    congr 1
    funext assignment
    exact (selectAssignment_of_subset included assignment).symm
  have targetSupport :
      ((μ.map (S.selectAssignment larger)).map forget).AlmostSurely
        (fun assignment => assignment ∈ S.selectedAssignmentEnumeration smaller) := by
    rw [sameMap]
    exact selectedSupport μ smaller
  have grouped := Distro.entropy_map_chain (μ.map (S.selectAssignment larger)) forget
    (S.selectedGrid larger) (S.selectedGrid smaller)
    (selectedSupport μ larger) targetSupport
    (S.selectedAssignmentEnumeration_complete larger)
    (S.selectedAssignmentEnumeration_complete smaller)
  have transported :
      ExactLog.Equiv
        (((μ.map (S.selectAssignment larger)).map forget).entropy
          (S.selectedGrid smaller) targetSupport)
        (selectedEntropy μ smaller) :=
    Distro.entropy_sameLaw (by rw [sameMap]; exact Distro.SameLaw.refl _)
      (S.selectedGrid smaller) targetSupport (selectedSupport μ smaller)
  exact ExactLog.equiv_trans grouped
    (ExactLog.add_congr transported (ExactLog.equiv_refl _))

theorem selectedConditionalEntropy_eq_sub (μ : Distro S.Assignment)
    {smaller larger : NodeSet S} (included : NodeSet.Subset smaller larger) :
    ExactLog.Equiv (selectedConditionalEntropy μ smaller larger)
      (ExactLog.sub (selectedEntropy μ larger) (selectedEntropy μ smaller)) :=
  ExactLog.equiv_symm (ExactLog.sub_eq_of_add (selectedEntropy_chain μ included))

theorem selectedConditionalEntropy_nonneg (μ : Distro S.Assignment)
    {smaller larger : NodeSet S} (_included : NodeSet.Subset smaller larger) :
    ExactLog.LE ExactLog.zero (selectedConditionalEntropy μ smaller larger) :=
  Distro.conditionalEntropyMap_nonneg _ _ _ _

/-- `I(left; right) = H(left) + H(right) - H(left,right)` on selected coordinates. -/
def selectedMutualInformation (μ : Distro S.Assignment)
    (left right : NodeSet S) : ExactLog :=
  mutualInformation (selectedEntropy μ left) (selectedEntropy μ right)
    (selectedEntropy μ (NodeSet.union left right))

/-- `I(left; right) = H(right) - H(right|left)`. -/
theorem selectedMutualInformation_eq_inner_minus_conditional
    (μ : Distro S.Assignment) (left right : NodeSet S) :
    ExactLog.Equiv (selectedMutualInformation μ left right)
      (ExactLog.sub (selectedEntropy μ right)
        (selectedConditionalEntropy μ left (NodeSet.union left right))) :=
  mutualInformation_eq_inner_minus_conditional
    (selectedEntropy μ left) (selectedEntropy μ right)
    (selectedEntropy μ (NodeSet.union left right))
    (selectedConditionalEntropy μ left (NodeSet.union left right))
    (selectedEntropy_chain μ (NodeSet.subset_union_left left right))

/-- `I(left; right | cond) = H(left,cond) + H(right,cond) - H(left,right,cond) - H(cond)`. -/
def selectedConditionalMutualInformation (μ : Distro S.Assignment)
    (left right cond : NodeSet S) : ExactLog :=
  ExactLog.sub
    (mutualInformation
      (selectedEntropy μ (NodeSet.union left cond))
      (selectedEntropy μ (NodeSet.union right cond))
      (selectedEntropy μ (NodeSet.union (NodeSet.union left right) cond)))
    (selectedEntropy μ cond)

end Causality
end Thesis
