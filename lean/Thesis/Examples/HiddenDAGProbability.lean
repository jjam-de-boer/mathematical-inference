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

/-! ## Unsupported conditionals remain distinct from supported zeros -/

/-- The earlier constant source has observational zeros but retains the
same canonical graph and independent root laws.  Its actual realization is
constructed without a positivity premise. -/
def zeroRealized : FiniteHiddenDAGSCM signature projection :=
  noiseModel.toHiddenDAGSCM noiseModel_compatible

def trueAssignment : signature.Assignment := fun _ => true

def nullConditional : Kernel signature :=
  ⟨NodeSet.singleton y, NodeSet.empty, NodeSet.singleton x⟩

def zeroUnconditional : Kernel signature :=
  ⟨NodeSet.singleton y, NodeSet.empty, NodeSet.empty⟩

/-- Conditioning on `X = true` in the constant source is undefined. -/
theorem source_null_conditional : nullConditional.denote noiseModel trueAssignment = none := by
  decide +kernel

/-- The native constructed model retains that missing conditional; it does
not turn `0 / 0` into zero or an arbitrary chosen conditional distribution. -/
theorem realized_null_conditional : zeroRealized.kernelDenote nullConditional trueAssignment = none := by
  decide +kernel

/-- Removing the null conditioner gives a supported zero outcome.  Testing
the present value's numerator avoids demanding a particular denominator
presentation for the rational zero. -/
theorem realized_supported_zero :
    (zeroRealized.kernelDenote zeroUnconditional trueAssignment).map (fun value => value.num) = some 0 := by
  decide +kernel

end HiddenDAGProbability
end Examples
end Causality
end Thesis
