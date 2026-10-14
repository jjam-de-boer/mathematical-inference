import Thesis.Causality.AlmostSureIntervention
import Thesis.Probability.FiniteRecordConsistencyBounds

namespace Thesis
namespace Causality
namespace Kernel

open Probability

/-!
# Intervention bounds supplied by unit-level SCM consistency

For any observed event, units already having the requested action values
retain their factual evaluation.  The remaining units can add at most their
entire probability mass.  The resulting lower and upper bounds use only the
whole observational distribution and apply to every finite latent SCM.

These are bounds on an unconditional event in the intervened distribution.
They do not divide by an observed or causal conditioner and must not be read
as bounds on an arbitrary conditional kernel.  The graph can impose tighter
bounds: sharpness for the unrestricted binary bow is proved separately by
constructing models that attain the endpoints.
-/

/-- Agreement with the action cylinder supplies the actual consistency
premise coordinate by coordinate.  This exposes the useful unit-level step
without imposing probability one on the entire action cylinder. -/
theorem evalUnder_eq_of_agreesOn (model : FiniteLatentSCM S) (kernel : Kernel S)
    (reference : S.Assignment) (unit : model.latent.Assignment)
    (selected : agreesOn kernel.action reference (model.eval unit) = true) :
    model.evalUnder (kernel.intervention reference) unit = model.eval unit := by
  apply model.evalUnder_consistency
  intro node value forced
  cases atAction : kernel.action node with
  | false =>
      simp only [intervention, atAction, Bool.false_eq_true, if_false] at forced
      cases forced
  | true =>
      have component := (finAll_eq_true_iff _).mp selected node
      have factual : model.eval unit node = reference node := by
        apply of_decide_eq_true
        simpa only [atAction, if_true] using component
      have fixed : reference node = value := by
        simpa only [intervention, atAction, if_true, Option.some.injEq] using forced
      exact factual.trans fixed

/-- Consistency sandwiches the genuine causal event between its factual
action-and-event mass and that mass plus the probability of other actions.
All three probabilities are unconditional and remain defined at zeros. -/
theorem distribution_consistency_bounds (model : FiniteLatentSCM S)
    (kernel : Kernel S) (reference : S.Assignment) (event : Event S.Assignment) :
    QProb.LE
        (model.observationalDist.probVal (fun sample => agreesOn kernel.action reference sample && event sample))
        ((kernel.distribution model reference).probVal event) ∧
      QProb.LE ((kernel.distribution model reference).probVal event)
        (QProb.add
          (model.observationalDist.probVal (fun sample => agreesOn kernel.action reference sample && event sample))
          (model.observationalDist.probVal (fun sample => !agreesOn kernel.action reference sample))) := by
  let evidence : Event model.latent.Assignment := fun unit => agreesOn kernel.action reference (model.eval unit)
  let factual : Event model.latent.Assignment := fun unit => event (model.eval unit)
  let alternative : Event model.latent.Assignment := fun unit =>
    event (model.evalUnder (kernel.intervention reference) unit)
  have priorBounds := model.prior.probVal_consistency_bounds evidence factual alternative
    (fun unit selected => congrArg event (evalUnder_eq_of_agreesOn model kernel reference unit selected))
  have lower := model.prior.map_probVal model.eval
    (fun sample => agreesOn kernel.action reference sample && event sample)
  have outside := model.prior.map_probVal model.eval
    (fun sample => !agreesOn kernel.action reference sample)
  have causal := distribution_probVal model kernel reference event
  exact ⟨QProb.le_congr (QProb.equiv_symm lower) (QProb.equiv_symm causal) priorBounds.1,
    QProb.le_congr (QProb.equiv_symm causal)
      (QProb.equiv_symm (QProb.add_congr lower outside)) priorBounds.2⟩

end Kernel
end Causality
end Thesis
