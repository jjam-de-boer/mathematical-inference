import Thesis.Examples.AlternativeFormulaSelection
import Thesis.CausalTransport.HiddenDAGConsistencyBounds

namespace Thesis
namespace Causality
namespace Examples
namespace ConsistencyBounds

open Probability
open AlternativeFormulaSelection

/-!
# Nontrivial native consistency bounds with zero-containing outcomes

Reuse the actual four-node SCM, whose requested effect is one half.  Its
factual action-and-outcome mass is one quarter and the probability of other
actions is one half, so the general consistency interval is `[1/4, 3/4]`.
The interval theorem below comes from native SCM consistency, independently
of the adjustment witnesses that compute the exact effect in this graph.

This example deliberately does not assert sharpness: the observed graph has
measured covariates that identify a tighter answer.  The separate bow result
must show endpoint attainment in its own full model class, rather than
mistaking universal bounds for sharp bounds on every causal graph.
-/

def kernel : Kernel signature := ⟨query.outcome, query.action, NodeSet.empty⟩

def outcome : Event signature.Assignment := Kernel.agreesOn query.outcome reference

def lower : QProb := model.observationalDist.probVal
  (fun sample => Kernel.agreesOn query.action reference sample && outcome sample)

def upper : QProb := QProb.add lower
  (model.observationalDist.probVal (fun sample => !Kernel.agreesOn query.action reference sample))

def effect : QProb := (model.kernelDistribution kernel reference).probVal outcome

/-- The general native theorem proves the interval without calculation of
this fixture's intervention, observational masses, or adjustment formula. -/
theorem native_consistency_interval : QProb.LE lower effect ∧ QProb.LE effect upper :=
  model.kernelDistribution_consistency_bounds kernel reference outcome

def quarter : QProb := ⟨1, 4, by decide⟩
def threeQuarters : QProb := ⟨3, 4, by decide⟩

theorem lower_is_quarter : QProb.Equiv lower quarter := by decide +kernel
theorem upper_is_threeQuarters : QProb.Equiv upper threeQuarters := by decide +kernel
theorem effect_is_half : QProb.Equiv effect half := by decide +kernel

/-- The numerical presentation is transferred by fraction equivalence,
not by equality of unreduced numerator/denominator records. -/
theorem displayed_consistency_interval : QProb.LE quarter half ∧ QProb.LE half threeQuarters :=
  ⟨QProb.le_congr lower_is_quarter effect_is_half native_consistency_interval.1,
    QProb.le_congr effect_is_half upper_is_threeQuarters native_consistency_interval.2⟩

end ConsistencyBounds
end Examples
end Causality
end Thesis
