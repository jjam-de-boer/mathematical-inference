import Thesis.Causality.SupportAwareSemantics
import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Causality

open Probability

/-!
# Weighted conditional identities for finite records containing zeros

The abstract weighted chain identity requires a dominated numerator.  Here
that condition is discharged for actual finite event probabilities: a joint
event is contained in its conditioning event, so zero conditioning mass
forces zero joint mass.

These identities apply to any `FiniteProbRecord`, including the observational
and interventional pushforwards of an SCM.  They do not require a positive
observed joint distribution.  They also do not identify an unsupported causal
action: their conclusion concerns a weighted probability identity within one
given distribution, not equality of effects across observationally equivalent
models.
-/

namespace ProbabilityResult

/-- Recover a finite-record joint mass by its guarded conditional contribution.
Containment discharges the zero-cell premise internally, even when the
displayed conditional ratio is undefined. -/
def weightedConditionalJoint (record : FiniteProbRecord Ω)
    (outcome condition : Event Ω) :
    Equivalent
      (weightedMultiply (some (record.probVal condition))
        (divide (some (record.probVal (Probability.inter outcome condition)))
          (some (record.probVal condition))))
      (some (record.probVal (Probability.inter outcome condition))) := by
  apply weightedMultiply_divide_cancel_of_le
  exact Nat.mul_le_mul_right record.den
    (FiniteProbRecord.eventMass_mono record.atoms
      (Probability.inter outcome condition) condition
      (fun _ selected => (Bool.and_eq_true_iff.mp selected).2))

/-- Summing finitely many guarded conditional contributions recovers the sum
of their actual joint masses, without imposing support on zero-mass conditions.
The conditions need not form a partition for this identity.  Identifying this
sum with the outcome marginal additionally requires the appropriate finite
partition or enumeration theorem at the caller's compilation boundary. -/
noncomputable def weightedConditionalContributions (record : FiniteProbRecord Ω)
    (values : List X) (outcome : Event Ω) (condition : X -> Event Ω) :
    Equivalent
      (weightedSum values (fun value => some (record.probVal (condition value)))
        (fun value => divide
          (some (record.probVal (Probability.inter outcome (condition value))))
          (some (record.probVal (condition value)))))
      (sum (values.map (fun value =>
        some (record.probVal (Probability.inter outcome (condition value)))))) :=
  sum_map_congr values _ _ (fun value =>
    weightedConditionalJoint record outcome (condition value))

end ProbabilityResult
end Causality
end Thesis
