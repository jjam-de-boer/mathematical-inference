import Thesis.CausalTransport.HiddenDAGProbability
import Thesis.Examples.HiddenDAGRealization

namespace Thesis
namespace Causality
namespace Examples
namespace HiddenDAGProbability

open Probability HiddenDAGCollapse HiddenDAGRootPlacement HiddenDAGRealization

/-!
# Probability regressions for the original-DAG realization

Use the nontrivial five-node relay fixture with one unused root, one private
input and three independent shared inputs installed at the same hidden node.
The allocated model omits the unused random coordinate, so literal atom-list
equality would be the wrong test; arbitrary observed event probabilities must
instead agree.

The concrete source and native joint-event computations below are checked
independently by the kernel.  The final theorem specializes the general
probability-preservation law to every intervention and observed Boolean event.
No fixture-specific preservation interface is assumed.
-/

/-- The unused bit doubles the source prior's atom list but contributes no
allocated channel.  Equality of probability laws must therefore not require
equality of these literal finite-record presentations. -/
theorem unused_root_changes_atom_count :
    sourceModel.prior.atoms.length = 32 ∧ realized.prior.atoms.length = 16 := by
  decide +kernel

def xAndYTrue : signature.Assignment → Bool :=
  fun assignment => assignment x && assignment y

/-- The source's two-coordinate event has probability one quarter. -/
theorem source_joint_probability : QProb.Equiv (sourceModel.observationalValue xAndYTrue)
    ⟨1, 4, by decide⟩ := by
  decide +kernel

/-- The actual constructed full-DAG prior and relay evaluator independently
give the same joint probability, not just the same one-channel marginals. -/
theorem realized_joint_probability : QProb.Equiv (realized.observationalValue xAndYTrue)
    ⟨1, 4, by decide⟩ := by
  decide +kernel

/-- The full general theorem specializes to this fixture for all events
and interventions.  This includes events depending on several observed nodes
and interventions whose signal must travel through the hidden relay. -/
theorem all_interventions_probability_agree (intervention : HardIntervention signature)
    (event : signature.Assignment → Bool) :
    QProb.Equiv (realized.interventionalValue intervention event)
      (sourceModel.interventionalValue intervention.value event) :=
  sourceModel.toHiddenDAGSCM_interventionalValue source_compatible intervention event

end HiddenDAGProbability
end Examples
end Causality
end Thesis
