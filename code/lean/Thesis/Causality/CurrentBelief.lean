import Thesis.Causality.ExtensionalMode
import Thesis.Causality.SharedResponseModel

namespace Thesis.Causality.ExtensionalMode
open Probability

/-!
# Causal evaluation under a current epistemic belief

The SCM's prior describes its generative population; a mode's belief may
have been updated by evidence.  These are two different laws on the same
mechanisms.  Updating can correlate originally independent source variables,
so the original projected graph cannot simply be reused as a certificate
for the updated observational table.

Every finite current belief nevertheless has a legitimate SCM representation.
For each latent assignment, collect all deterministic local response rows;
push the current belief onto that finite response carrier; use the existing
one-shared-root constructor.  The resulting graph admits arbitrary shared
dependence.  This is a conservative representation of the epistemic law,
not evidence of additional physical arrows in the original system.

The preservation theorem below is uniform over every hard intervention and
every Boolean event.  Consequently it also preserves the denominators used
to ask supported conditional questions.  No positivity, bound on rational
denominators, or independence of the current belief is assumed.
-/

variable {S : ObservedSignature.{0}}

/-- Joint law of the mechanism-response tables under the current belief.
Null and repeated atoms are retained by the existing pushforward operation. -/
def currentResponseLaw (mode : ExtensionalMode S) :
    FiniteProbRecord (SharedResponse.Table S) :=
  mode.belief.map (SharedResponse.responseOf S mode.model)

/-- A valid generative representation of the current-belief semantics.
Its single source may feed every observed node, so callers must use this
representation's graph rather than silently assuming the original one. -/
def currentModel (mode : ExtensionalMode S) : ExactModel S :=
  SharedResponse.model S mode.currentResponseLaw

/-- Explicit model-conditional evaluation after abduction: operate on the
mechanisms while integrating over the mode's current latent information. -/
def currentInterventionalValue (mode : ExtensionalMode S)
    (action : HardIntervention S) (event : Event S.Assignment) : QProb :=
  (mode.belief.map (mode.model.evalUnder action.value)).probVal event

/-- The reconstructed SCM preserves the complete experimental family.
The proof uses pointwise response-table execution, followed by pushforward
identities; it does not infer an independence property of the posterior. -/
theorem currentModel_preserves (mode : ExtensionalMode S)
    (action : HardIntervention S) (event : Event S.Assignment) :
    QProb.Equiv (mode.currentModel.interventionalValue action.value event)
      (mode.currentInterventionalValue action event) := by
  apply QProb.equiv_trans (SharedResponse.model_interventionalValue S
    mode.currentResponseLaw action.value event)
  apply QProb.equiv_trans (mode.belief.map_probVal
    (SharedResponse.responseOf S mode.model)
    (fun table => event (SharedResponse.eval S action.value table)))
  apply QProb.equiv_trans (mode.belief.probVal_congr _ _ (fun unit =>
    congrArg event (SharedResponse.eval_responseOf S mode.model unit action.value)))
  exact QProb.equiv_symm (mode.belief.map_probVal
    (mode.model.evalUnder action.value) event)

/-- The conservative graph is stated explicitly, including all pairwise
bidirected edges.  It is not generally the original mode model's graph. -/
theorem currentModel_graph (mode : ExtensionalMode S) (first second : Fin S.count) :
    mode.currentModel.observedGraph.bidirected first second =
      (SharedResponse.graph S).bidirected first second :=
  SharedResponse.model_projectedGraph S mode.currentResponseLaw first second

end Thesis.Causality.ExtensionalMode
