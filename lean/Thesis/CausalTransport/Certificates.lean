import Thesis.Causality.Identification
import Thesis.CausalTransport.DSeparation

namespace Thesis
namespace Causality

open Probability

/-!
Generic inspectable certificates for a source probability term.

Both joint and conditional kernel queries reduce to a source
`ProbabilityTerm`; their identification certificates differ only in which
query supplies that term.  This module factors out that shared certificate
shape. `Correspondence` provides query-specific structures and explicit
adapters to this generic representation.
-/

/--
An inspectable action-free reduction of one source probability term.  The
support field supplies the recursive support tree required to interpret the
concrete do-calculus derivation in every compatible finite model.
-/
structure IdentificationCertificate (G : ObservedGraph S)
    (sourceTerm : ProbabilityTerm S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : DoCalculusDerivation G sourceTerm formula
  supported : forall model : ExactModel S, (compatible : Compatible model G) ->
    forall assignment, sourceTerm.SupportedAt model assignment ->
      LocalDerivationSupport model assignment derivation

/--
The corresponding pre-compilation certificate: its derivation is expressed
with active-path side conditions and is compiled only after d-separation
correctness has been supplied explicitly.
-/
structure PublishedIdentificationCertificate (G : ObservedGraph S)
    (correct : DSeparationCorrectness G) (sourceTerm : ProbabilityTerm S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G sourceTerm formula
  supported : forall model : ExactModel S, (compatible : Compatible model G) ->
    forall assignment, sourceTerm.SupportedAt model assignment ->
      LocalDerivationSupport model assignment (derivation.compile correct)

/-- Compile path-based side conditions into the executable derivation syntax. -/
def PublishedIdentificationCertificate.compile
    (certificate : PublishedIdentificationCertificate G correct sourceTerm) :
    IdentificationCertificate G sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation.compile correct
  supported := certificate.supported

end Causality
end Thesis
