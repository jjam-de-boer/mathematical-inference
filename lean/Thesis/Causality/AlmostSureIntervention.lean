import Thesis.Probability.FiniteRecordAlmostSure
import Thesis.Causality.ObservationalSupport

namespace Thesis
namespace Causality

open Probability

/-!
# Interventions already factual with probability one

The hypothesis concerns the exact observational probability of the selected
action cylinder.  It is not a frequency-zero inference from a sample, nor a
graphical non-confounding premise.  Unit-level SCM consistency identifies the
two evaluations on that cylinder, and finite full-mass congruence removes
zero-weight exceptions.  The conclusion holds for every event and for all
finite latent alphabets, even when the graph-level ID algorithm fails.

Only this action value is covered.  Nothing here identifies a different
treatment value or a treatment contrast.  Conditional kernels retain their
ordinary partial meaning: a null conditioner is null on both sides, rather
than being assigned an arbitrary value.
-/

namespace Kernel

/-- Setting action coordinates to values already factual with probability
one preserves the whole observed law.  The proof uses the original prior,
not a selected model family or a global positivity assumption. -/
theorem distribution_eq_observational_of_action_one (model : FiniteLatentSCM S)
    (kernel : Kernel S) (reference : S.Assignment)
    (full : QProb.Equiv
      (model.observationalDist.probVal (agreesOn kernel.action reference)) QProb.one)
    (event : Event S.Assignment) :
    QProb.Equiv ((kernel.distribution model reference).probVal event)
      (model.observationalDist.probVal event) := by
  let evidence : Event model.latent.Assignment := fun unit =>
    agreesOn kernel.action reference (model.eval unit)
  have priorFull : QProb.Equiv (model.prior.probVal evidence) QProb.one :=
    QProb.equiv_trans
      (QProb.equiv_symm (model.prior.map_probVal model.eval
        (agreesOn kernel.action reference))) full
  have consistent : forall unit, evidence unit = true →
      model.evalUnder (kernel.intervention reference) unit = model.eval unit := by
    intro unit selected
    apply model.evalUnder_consistency
    intro node value forced
    cases selectedAction : kernel.action node with
    | false =>
        simp only [intervention, selectedAction, Bool.false_eq_true, if_false] at forced
        cases forced
    | true =>
        have component := (finAll_eq_true_iff _).mp selected node
        have factual : model.eval unit node = reference node := by
          apply of_decide_eq_true
          simpa only [selectedAction, if_true] using component
        have fixed : reference node = value := by
          simpa only [intervention, selectedAction, if_true, Option.some.injEq] using forced
        exact factual.trans fixed
  exact QProb.equiv_trans (distribution_probVal model kernel reference event)
    (QProb.equiv_trans
      (model.prior.probVal_congr_on_probability_one evidence
        (fun unit => event (model.evalUnder (kernel.intervention reference) unit))
        (fun unit => event (model.eval unit)) priorFull
        (fun unit selected => congrArg event (consistent unit selected)))
      (QProb.equiv_symm (model.prior.map_probVal model.eval event)))

/-- The complete partial conditional result agrees with its observational
counterpart.  Numerators and denominators are preserved separately, so this
includes supported zeros and also preserves undefined conditioners. -/
noncomputable def denote_eq_observational_of_action_one (model : FiniteLatentSCM S)
    (kernel : Kernel S) (reference : S.Assignment)
    (full : QProb.Equiv
      (model.observationalDist.probVal (agreesOn kernel.action reference)) QProb.one) :
    ProbabilityResult.Equivalent (kernel.denote model reference)
      ((⟨kernel.outcome, NodeSet.empty, kernel.condition⟩ : Kernel S).denote model reference) := by
  let observed : Kernel S := ⟨kernel.outcome, NodeSet.empty, kernel.condition⟩
  have noAction : observed.hasAction = false :=
    ProbabilityTerm.actionFree_hasAction_false observed (fun _ => rfl)
  have distribution : observed.distribution model reference = model.observationalDist := by
    simp only [Kernel.distribution, noAction, Bool.false_eq_true, if_false]
  change ProbabilityResult.Equivalent (kernel.denote model reference) (observed.denote model reference)
  unfold Kernel.denote
  rw [distribution]
  exact ProbabilityResult.divide_congr
    (.value (distribution_eq_observational_of_action_one model kernel reference full _))
    (.value (distribution_eq_observational_of_action_one model kernel reference full _))

end Kernel
end Causality
end Thesis
