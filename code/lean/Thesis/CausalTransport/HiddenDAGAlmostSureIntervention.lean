import Thesis.Causality.AlmostSureIntervention
import Thesis.CausalTransport.HiddenDAGSemantics

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {P : FiniteLatentProjection S}

/-!
# Native hidden-DAG consequences of a probability-one action

The guard is an event probability in the original observational record.
The proved intervention-preserving collapse transfers the intrinsic finite
consistency theorem back to that original model, including arbitrary finite
hidden and private-noise sizes.  This is a distribution-specific theorem,
not an additional unqualified do-calculus rule or graph-level success claim.
-/

namespace FiniteHiddenDAGSCM

/-- Native causal and observational kernels agree when the action is already
factual with probability one.  The original condition set is left intact. -/
noncomputable def kernel_eq_observational_of_action_one (model : FiniteHiddenDAGSCM S P)
    (kernel : Kernel S) (reference : S.Assignment)
    (full : QProb.Equiv
      (model.observationalDist.probVal (Kernel.agreesOn kernel.action reference)) QProb.one) :
    model.TermEquivalentAt (.kernel kernel)
      (.kernel ⟨kernel.outcome, NodeSet.empty, kernel.condition⟩) reference := by
  apply model.termEquivalentAt_of_collapsed
  apply Kernel.denote_eq_observational_of_action_one model.toLatentRootSCM kernel reference
  rw [model.toLatentRootSCM_observationalDist]
  exact full

/-- Whole observed-law agreement transfers the observable probability-one
guard, independently of hidden mechanisms or hidden alphabet sizes. -/
theorem action_probability_one_transfer {left right : FiniteHiddenDAGSCM S P}
    (observational : left.ObservationalAgreement right) (action : NodeSet S)
    (reference : S.Assignment)
    (full : QProb.Equiv
      (left.observationalDist.probVal (Kernel.agreesOn action reference)) QProb.one) :
    QProb.Equiv
      (right.observationalDist.probVal (Kernel.agreesOn action reference)) QProb.one :=
  QProb.equiv_trans (QProb.equiv_symm (observational (Kernel.agreesOn action reference))) full

/-- Two actual native models identify this action's query value under the
shared probability-one guard.  This makes no claim about other action values.
Partial conditional results are compared without completing null events. -/
noncomputable def kernel_identifiable_of_action_one
    (left right : FiniteHiddenDAGSCM S P) (observational : left.ObservationalAgreement right)
    (kernel : Kernel S) (reference : S.Assignment)
    (full : QProb.Equiv
      (left.observationalDist.probVal (Kernel.agreesOn kernel.action reference)) QProb.one) :
    ProbabilityResult.Equivalent (left.kernelDenote kernel reference) (right.kernelDenote kernel reference) :=
  ProbabilityResult.trans (left.kernel_eq_observational_of_action_one kernel reference full)
    (ProbabilityResult.trans
      (actionFree_invariant left right observational
        (.kernel ⟨kernel.outcome, NodeSet.empty, kernel.condition⟩) (fun _ => rfl) reference)
      (ProbabilityResult.symm (right.kernel_eq_observational_of_action_one kernel reference
        (action_probability_one_transfer observational kernel.action reference full))))

end FiniteHiddenDAGSCM
end Causality
end Thesis
