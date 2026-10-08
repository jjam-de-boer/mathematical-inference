import Thesis.Causality.Identification

namespace Thesis
namespace Causality

open Probability

/-!
# Conditional kernels as genuinely conditioned latent priors

A kernel samples a model's evaluated observed distribution, whereas a private
noise construction works directly with its latent prior.  The theorem below
connects those two presentations at the same reference-compatible action.
Both numerator and denominator are transported before division; the support
witness belongs to that actual pulled-back conditioning event.

This intrinsic semantic identity uses no graph assumption, positivity axiom,
or do-calculus soundness.  Its companion support theorem derives the latent
context support from ordinary observational positivity and finite SCM
consistency, without selecting a latent realization of the reference.
-/

/-- Every reference cylinder remains supported under its own kernel action.
This is prior-level support, including the executable no-action branch. -/
theorem ObservationallyPositive.kernel_prior_cylinder_positive
    {S : ObservedSignature} {model : ExactModel S} (positive : ObservationallyPositive model)
    (kernel : Kernel S) (nodes : NodeSet S) (reference : S.Assignment) :
    model.prior.EventPositive (fun unit => Kernel.agreesOn nodes reference
      (model.evalUnder (kernel.intervention reference) unit)) :=
  (QProb.equiv_num_pos_iff (Kernel.distribution_probVal model kernel reference
    (Kernel.agreesOn nodes reference))).mp
      (positive.kernel_cylinder_positive kernel nodes reference)

/-- A supported kernel cell equals the conditional prior probability of
its full outcome cylinder after the same intervention.  The prior need not
be positive on every event, and no equality of unrelated denominators is
assumed. -/
noncomputable def Kernel.denote_prior_conditionOn
    {S : ObservedSignature} (model : ExactModel S) (kernel : Kernel S) (reference : S.Assignment)
    (supported : model.prior.EventPositive (fun unit => kernel.conditionEvent reference
      (model.evalUnder (kernel.intervention reference) unit))) :
    ProbabilityResult.Equivalent (kernel.denote model reference)
      (some ((model.prior.conditionOn (fun unit => kernel.conditionEvent reference
          (model.evalUnder (kernel.intervention reference) unit)) supported).probVal
        (fun unit => Kernel.agreesOn kernel.outcome reference
          (model.evalUnder (kernel.intervention reference) unit)))) := by
  let context := fun unit => kernel.conditionEvent reference
    (model.evalUnder (kernel.intervention reference) unit)
  let outcome := fun unit => Kernel.agreesOn kernel.outcome reference
    (model.evalUnder (kernel.intervention reference) unit)
  have denominator := Kernel.distribution_probVal model kernel reference (kernel.conditionEvent reference)
  have numerator := QProb.equiv_trans
    (Kernel.distribution_probVal model kernel reference (kernel.numeratorEvent reference))
    (model.prior.probVal_congr _ (fun unit => context unit && outcome unit)
      (fun unit => Bool.and_comm _ _))
  have kernelSupported := (QProb.equiv_num_pos_iff denominator).mpr supported
  have kernelValue : ProbabilityResult.Equivalent (kernel.denote model reference)
      (some (QProb.div ((kernel.distribution model reference).probVal (kernel.numeratorEvent reference))
        ((kernel.distribution model reference).probVal (kernel.conditionEvent reference)) kernelSupported)) := by
    unfold Kernel.denote
    rw [ProbabilityResult.divide, dif_pos kernelSupported]
    exact .value (QProb.equiv_refl _)
  exact ProbabilityResult.trans kernelValue (.value
    (QProb.equiv_trans (QProb.div_congr numerator denominator kernelSupported supported)
      (QProb.equiv_symm (model.prior.conditionOn_probVal context outcome supported))))

end Causality
end Thesis
