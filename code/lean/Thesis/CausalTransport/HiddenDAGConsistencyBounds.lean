import Thesis.Causality.ConsistencyBounds
import Thesis.CausalTransport.HiddenDAGSemantics

namespace Thesis
namespace Causality
namespace FiniteHiddenDAGSCM

open Probability

variable {S : ObservedSignature} {P : FiniteLatentProjection S}

/-!
# Consistency bounds in the original finite hidden-DAG model

The lower and upper expressions below are probabilities in the native
observational record.  The intervened event is evaluated by the native SCM,
not defined via a projected or canonical replacement model.  The proved
intervention-preserving collapse transfers the intrinsic consistency bound
back to these exact original records, for arbitrary finite hidden and noise
domains.  Sharpness in the bow class remains a separate constructive task.
-/

/-- Native causal-event bounds require no observed positivity, separation,
faithfulness, or external identification interface.  The kernel's condition
field is not used: this is an unconditional intervened-event statement. -/
theorem kernelDistribution_consistency_bounds (model : FiniteHiddenDAGSCM S P)
    (kernel : Kernel S) (reference : S.Assignment) (event : Event S.Assignment) :
    QProb.LE
        (model.observationalDist.probVal
          (fun sample => Kernel.agreesOn kernel.action reference sample && event sample))
        ((model.kernelDistribution kernel reference).probVal event) ∧
      QProb.LE ((model.kernelDistribution kernel reference).probVal event)
        (QProb.add
          (model.observationalDist.probVal
            (fun sample => Kernel.agreesOn kernel.action reference sample && event sample))
          (model.observationalDist.probVal
            (fun sample => !Kernel.agreesOn kernel.action reference sample))) := by
  rw [model.kernelDistribution_preserved, ← model.toLatentRootSCM_observationalDist]
  exact Kernel.distribution_consistency_bounds model.toLatentRootSCM kernel reference event

end FiniteHiddenDAGSCM
end Causality
end Thesis
