import Thesis.Causality.CurrentBelief
import Thesis.Causality.Counterfactual

namespace Thesis.Causality.ExtensionalMode
open Probability

/-!
# Evaluating finite counterfactual queries at a mode's current belief

A response table stores all local responses for one latent unit. The
current-belief representation pushes each unit to its entire table together,
so each potential-outcome atom keeps its original shared unit coupling.
The following proof uses pointwise execution of this table in every world.
It therefore preserves Boolean combinations of atoms and the partial
conditional probability formed from any two such events.

The coupling comes from the supplied model and its current latent belief.
Separate observed or interventional marginals alone do not determine it.
This module provides model-conditional evaluation and a representation
theorem; identification of a counterfactual from observed data is a separate
question.
-/

variable {S : ObservedSignature.{0}}

/-- Put the source unit's entire response table at the represented model's
single root. Every occurrence of that unit uses this same table. -/
def responseUnit (mode : ExtensionalMode S) (unit : mode.model.latent.Assignment) :
    mode.currentModel.latent.Assignment :=
  fun _ => SharedResponse.responseOf S mode.model unit

/-- A hypothetical setting preserves the whole output assignment at the
encoded unit. The first step unfolds the common-root executor, and the
second is the original local response-table simulation theorem. -/
theorem responseUnit_eval (mode : ExtensionalMode S)
    (unit : mode.model.latent.Assignment) (target : (i : Fin S.count) → Option (S.Value i)) :
    mode.currentModel.evalUnder target (mode.responseUnit unit) =
      mode.model.evalUnder target unit :=
  (SharedResponse.model_eval S mode.currentResponseLaw target (mode.responseUnit unit)).trans
    (SharedResponse.eval_responseOf S mode.model unit target)

/-- Potential-outcome atoms commute with this encoding, and induction
retains the same unit on both sides of every Boolean connective. -/
theorem responseUnit_holds (mode : ExtensionalMode S) (event : CounterfactualEvent S)
    (unit : mode.model.latent.Assignment) :
    event.holds mode.currentModel (mode.responseUnit unit) = event.holds mode.model unit := by
  induction event with
  | truth => rfl
  | falsity => rfl
  | atom atom =>
      unfold CounterfactualEvent.holds CounterfactualAtom.holds
      rw [responseUnit_eval]
  | conj left right leftIH rightIH => simp [CounterfactualEvent.holds, leftIH, rightIH]
  | disj left right leftIH rightIH => simp [CounterfactualEvent.holds, leftIH, rightIH]
  | neg inner ih => simp [CounterfactualEvent.holds, ih]

/-- Evaluate a whole multiworld event by integrating over the updated latent
belief, using the stored mechanisms in each atom's named intervention. -/
def currentCounterfactualEvent (mode : ExtensionalMode S) (event : CounterfactualEvent S) :
    QProb :=
  mode.belief.probVal (event.holds mode.model)

/-- Two pushforwards encode the latent unit without changing event mass.
Pointwise event agreement supplies the final change of predicate. -/
theorem currentModel_preserves_counterfactualEvent (mode : ExtensionalMode S)
    (event : CounterfactualEvent S) :
    QProb.Equiv (mode.currentModel.prior.probVal (event.holds mode.currentModel))
      (mode.currentCounterfactualEvent event) := by
  apply QProb.equiv_trans (mode.currentResponseLaw.map_probVal
    (fun table _ => table) (event.holds mode.currentModel))
  apply QProb.equiv_trans (mode.belief.map_probVal (SharedResponse.responseOf S mode.model)
    (fun table => event.holds mode.currentModel (fun _ => table)))
  exact mode.belief.probVal_congr _ _ (mode.responseUnit_holds event)

/-- The partial conditional keeps a zero-mass conditioner undefined.
The numerator is a conjunction on one shared unit, not a product of
separately sampled intervention probabilities. -/
def currentCounterfactual (mode : ExtensionalMode S) (query : CounterfactualQuery S) :
    ProbabilityResult.Result :=
  ProbabilityResult.divide
    (some (mode.currentCounterfactualEvent (.conj query.condition query.outcome)))
    (some (mode.currentCounterfactualEvent query.condition))

/-- Representation preserves the partial answer, including both a supported
zero numerator and an unsupported conditioner. -/
noncomputable def currentModel_preserves_counterfactual (mode : ExtensionalMode S)
    (query : CounterfactualQuery S) :
    ProbabilityResult.Equivalent (query.denote mode.currentModel)
      (mode.currentCounterfactual query) :=
  ProbabilityResult.divide_congr
    (.value (mode.currentModel_preserves_counterfactualEvent (.conj query.condition query.outcome)))
    (.value (mode.currentModel_preserves_counterfactualEvent query.condition))

end Thesis.Causality.ExtensionalMode
