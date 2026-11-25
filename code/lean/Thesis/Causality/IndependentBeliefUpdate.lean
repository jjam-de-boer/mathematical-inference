import Thesis.Causality.HardIntervention
import Thesis.Probability.IndependentConditioning

namespace Thesis.Causality.FiniteLatentSCM
open Probability

/-!
# A certified class of epistemic updates preserving the source graph

Each latent source may be conditioned on its own supported evidence. The
joint observation is a rectangle in the latent assignment space, so the
finite product-conditioning theorem proves that the posterior sources
remain independent. This is a sufficient update discipline, not a claim
that arbitrary evidence preserves independence.

`conditionSources` packages the posterior as a new generative SCM with the
same source incidence and structural equations. Thus its projected graph
is literally the old one, while its prior and source factors reflect the
new information. The constructor is useful when an epistemic application
can justify source-wise evidence; general current beliefs instead use the
shared-response representation from `CurrentBelief`.
-/

variable {S : ObservedSignature.{0}}

/-- Expose the SCM's existing independent latent law without changing its
presentation or recomputing any source factor. -/
def independentSourceLaw (model : ExactModel S) :
    FiniteProduct.IndependentLaw model.latent.Value where
  factor := model.factor
  prior := model.prior
  product_law := model.product_law

/-- Supported source-wise evidence gives a complete updated SCM. The
product law is proved by conditioning the joint prior, rather than simply
asserted for a separately installed collection of posterior factors. -/
def conditionSources (model : ExactModel S)
    (evidence : (source : Fin model.latent.count) → Event (model.latent.Value source))
    (supported : ∀ source, (model.factor source).EventPositive (evidence source)) :
    ExactModel S where
  latent := model.latent
  factor := (model.independentSourceLaw.condition evidence supported).factor
  prior := (model.independentSourceLaw.condition evidence supported).prior
  product_law := (model.independentSourceLaw.condition evidence supported).product_law
  mechanism := model.mechanism

/-- The operation preserves causal incidence exactly; it adds no latent
edge merely to account for dependence that this update theorem excludes. -/
theorem conditionSources_graph (model : ExactModel S)
    (evidence : (source : Fin model.latent.count) → Event (model.latent.Value source))
    (supported : ∀ source, (model.factor source).EventPositive (evidence source)) :
    (model.conditionSources evidence supported).observedGraph = model.observedGraph :=
  rfl

/-- The updated prior is the actual Bayesian restriction of the original
joint prior. This equation makes the provenance of the new population law
explicit even though its independent factors have also been retained. -/
theorem conditionSources_prior (model : ExactModel S)
    (evidence : (source : Fin model.latent.count) → Event (model.latent.Value source))
    (supported : ∀ source, (model.factor source).EventPositive (evidence source)) :
    (model.conditionSources evidence supported).prior =
      model.prior.conditionOn
        (FiniteProduct.rectangularEvent model.latent.count model.latent.Value evidence)
        (model.independentSourceLaw.rectangular_positive evidence supported) :=
  rfl

end Thesis.Causality.FiniteLatentSCM
