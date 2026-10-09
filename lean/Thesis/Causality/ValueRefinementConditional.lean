import Thesis.Causality.BinaryRecoding
import Thesis.Causality.Identification

namespace Thesis
namespace Causality
namespace ObservedValueRefinement

open Probability

/-!
# Preserving an arbitrary binary conditional cell on the original alphabet

Joint probability preservation alone does not preserve a conditional gap:
the evidence probabilities may differ in the two models.  Instead, transport
the numerator and the denominator of each model's same supported cell
separately.  Their equality across models is neither needed nor asserted.

For a supplied Boolean reference, an explicit coordinate recoding sends
that reference to bit one at every node.  Deterministic encoding represents
bit one by the unique distinguished `second` label.  The ordinary private
label refinement keeps every bit and never changes that label.  Consequently
each full-label cylinder at the all-second reference is exactly a decoded
bit-one cylinder, including cylinders on the conditioner.  No averaging over
bit-zero label fibres or equality of their context weights is required.

Both transformations retain the original graph, action, outcome and condition
sets.  The all-second action is decoded back to the supplied original Boolean
action reference, so the separated intervention is not silently changed.
The final kernel comparison is valid even when a cell is unsupported: the
existing partial-ratio congruence transports the actual support status.
Positivity of the final model is an independent obligation of its constructor.

These are general SCM transports; they use neither soundness nor a supplied
conditional counterexample.  The one-way assembly companion applies them
to the actual finite separated cell of a positive Boolean countermodel.
-/

variable {S : ObservedSignature.{0}}

/-- The explicit mask sending the supplied Boolean reference to bit one.
It is computed coordinatewise, not selected from a propositional existence. -/
def cellMask (reference : S.binary.Assignment) : S.binary.Assignment :=
  fun node => Bool.not (reference node)

/-- The final original-alphabet SCM for one supplied binary source cell.
Recoding and encoding do not change its latent data; only the already
verified independent private label sweep supplies the additional labels. -/
def cellModel (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    (reference : S.binary.Assignment) : ExactModel S :=
  refine rich (BinaryEncoding.model rich (BinaryRecoding.model (cellMask reference) base))

/-- At the all-second reference, full-label agreement is exactly bit-one
agreement on the same selected coordinates, for every original assignment.
This relies on bit one's singleton fibre, not on a two-label alphabet. -/
theorem agreesOn_secondReference (rich : ObservedSignature.ValueRich S)
    (nodes : NodeSet S) (sample : S.Assignment) :
    Kernel.agreesOn nodes rich.second sample =
      Kernel.agreesOn (S := S.binary) nodes (fun _ => true) (bits (S := S) rich sample) := by
  unfold Kernel.agreesOn
  apply finAll_congr
  intro node
  cases selected : nodes node with
  | false => rfl
  | true =>
      simp only [if_true]
      change bit rich node (sample node) = decide (bit rich node (sample node) = true)
      cases bit rich node (sample node) <;> rfl

/-- A bit-one cylinder after the explicit recoding is precisely the source
reference cylinder.  Every selected coordinate is checked, including mixed
references with different Boolean values at different nodes. -/
theorem agreesOn_recodedReference (nodes : NodeSet S)
    (reference sample : S.binary.Assignment) :
    Kernel.agreesOn (S := S.binary) nodes (fun _ => true)
      (BinaryRecoding.assignment (cellMask reference) sample) =
      Kernel.agreesOn (S := S.binary) nodes reference sample := by
  unfold Kernel.agreesOn
  apply finAll_congr
  intro node
  cases selected : nodes node with
  | false => rfl
  | true =>
      simp only [if_true]
      change decide (Bool.xor (sample node) (Bool.not (reference node)) = true) =
        decide (sample node = reference node)
      cases sample node <;> cases reference node <;> rfl

/-- The all-second intervention recovers the source cell's entire action,
not only a seed or a convenient action value.  Unacted coordinates stay free. -/
theorem cellIntervention (query : ConditionalKernelQuery S) (rich : ObservedSignature.ValueRich S)
    (reference : S.binary.Assignment) :
    BinaryRecoding.intervention (cellMask reference)
      (BinaryEncoding.intervention rich (query.operationKernel.intervention rich.second)) =
      query.binary.operationKernel.intervention reference := by
  funext node
  cases selected : query.action node with
  | false =>
      simp only [BinaryRecoding.intervention, BinaryEncoding.intervention, Kernel.intervention,
        ConditionalKernelQuery.operationKernel, ConditionalKernelQuery.binary, selected,
        Bool.false_eq_true, if_false, Option.map_none]
      rfl
  | true =>
      simp only [BinaryRecoding.intervention, BinaryEncoding.intervention, Kernel.intervention,
        ConditionalKernelQuery.operationKernel, ConditionalKernelQuery.binary, selected, if_true, Option.map_some]
      have secondBit : bit rich node (rich.second node) = true := decide_eq_true rfl
      rw [secondBit]
      simp only [cellMask]
      cases reference node <;> rfl

/-- Every bit-dependent interventional event in the final label-refined
model is the recoded event in the original Boolean model, with the actual
forced labels decoded in both stages.  No evidence normalization occurs yet. -/
theorem cellModel_interventionalBitsValue (rich : ObservedSignature.ValueRich S)
    (base : ExactModel S.binary) (reference : S.binary.Assignment)
    (target : (node : Fin S.count) -> Option (S.Value node)) (event : Event S.binary.Assignment) :
    QProb.Equiv ((cellModel rich base reference).interventionalValue target (fun sample => event (bits (S := S) rich sample)))
      (base.interventionalValue
        (BinaryRecoding.intervention (cellMask reference) (BinaryEncoding.intervention rich target))
        (fun sample => event (BinaryRecoding.assignment (cellMask reference) sample))) :=
  QProb.equiv_trans (refine_interventionalBitsValue rich _ (BinaryEncoding.respectsParentBits rich _) target event)
    (QProb.equiv_trans (BinaryEncoding.interventionalBitsValue rich _ target event)
      (BinaryRecoding.interventionalValue (cellMask reference) base _ event))

/-- Compare one actual selected cylinder before normalizing a conditional.
The same statement applies to the joint numerator and to the conditioner;
there is no premise that either of those masses agrees across two models. -/
theorem cellModel_cylinderValue (query : ConditionalKernelQuery S)
    (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    (reference : S.binary.Assignment) (nodes : NodeSet S) :
    QProb.Equiv
      ((query.operationKernel.distribution (cellModel rich base reference) rich.second).probVal
        (Kernel.agreesOn nodes rich.second))
      ((query.binary.operationKernel.distribution base reference).probVal
        (Kernel.agreesOn (S := S.binary) nodes reference)) := by
  let final := cellModel rich base reference
  let target := query.operationKernel.intervention rich.second
  let event : Event S.binary.Assignment := Kernel.agreesOn (S := S.binary) nodes (fun _ => true)
  have pulled := cellModel_interventionalBitsValue rich base reference target event
  change QProb.Equiv (final.interventionalValue target (fun sample => event (bits (S := S) rich sample)))
    (base.interventionalValue
      (@BinaryRecoding.intervention S (cellMask reference)
        (BinaryEncoding.intervention rich (query.operationKernel.intervention rich.second)))
      (fun sample => event (BinaryRecoding.assignment (cellMask reference) sample))) at pulled
  rw [@cellIntervention S query rich reference] at pulled
  have sourceEvent := (base.interventionalDist (query.binary.operationKernel.intervention reference)).probVal_congr
    (fun sample => event (BinaryRecoding.assignment (cellMask reference) sample))
    (Kernel.agreesOn (S := S.binary) nodes reference)
    (agreesOn_recodedReference nodes reference)
  have finalEvent := (final.interventionalDist target).probVal_congr
    (Kernel.agreesOn nodes rich.second) (fun sample => event (bits (S := S) rich sample))
    (agreesOn_secondReference rich nodes)
  have finalDistribution := QProb.equiv_trans
    (Kernel.distribution_probVal final query.operationKernel rich.second (Kernel.agreesOn nodes rich.second))
    (QProb.equiv_symm (final.interventionalValue_eq target (Kernel.agreesOn nodes rich.second)))
  have sourceDistribution := QProb.equiv_trans
    (Kernel.distribution_probVal base query.binary.operationKernel reference
      (Kernel.agreesOn (S := S.binary) nodes reference))
    (QProb.equiv_symm (base.interventionalValue_eq
      (query.binary.operationKernel.intervention reference) (Kernel.agreesOn (S := S.binary) nodes reference)))
  exact QProb.equiv_trans finalDistribution (QProb.equiv_trans finalEvent
    (QProb.equiv_trans pulled (QProb.equiv_trans sourceEvent (QProb.equiv_symm sourceDistribution))))

/-- The final full-label conditional cell has exactly the source Boolean
cell's value and support status.  Numerator and evidence probabilities are
transported on each model separately, then the partial ratios are compared.
Unequal conditioning masses between two source models are fully retained. -/
noncomputable def cellModel_conditionalCell (query : ConditionalKernelQuery S)
    (rich : ObservedSignature.ValueRich S) (base : ExactModel S.binary)
    (reference : S.binary.Assignment) :
    ProbabilityResult.Equivalent
      (query.sourceTerm.denote (cellModel rich base reference) rich.second)
      (query.binary.sourceTerm.denote base reference) := by
  change ProbabilityResult.Equivalent (query.operationKernel.denote _ rich.second)
    (query.binary.operationKernel.denote base reference)
  have numerator : query.operationKernel.numeratorEvent rich.second =
      Kernel.agreesOn (NodeSet.union query.outcome query.condition) rich.second := by
    funext sample
    exact (Kernel.agreesOn_union query.outcome query.condition rich.second sample).symm
  have binaryNumerator : query.binary.operationKernel.numeratorEvent reference =
      Kernel.agreesOn (S := S.binary) (NodeSet.union query.outcome query.condition) reference := by
    funext sample
    exact (Kernel.agreesOn_union (S := S.binary) query.outcome query.condition reference sample).symm
  unfold Kernel.denote
  rw [numerator, binaryNumerator]
  exact ProbabilityResult.divide_congr
    (.value (cellModel_cylinderValue query rich base reference (NodeSet.union query.outcome query.condition)))
    (.value (cellModel_cylinderValue query rich base reference query.condition))

end ObservedValueRefinement
end Causality
end Thesis
