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

Support is demanded only inside a selected `GraphModelClass`.  The classical
completeness inhabitant uses the strictly positive subclass; the SCM layer
continues to admit observational zeros.
-/

/--
An inspectable action-free reduction of one source probability term.  The
support field supplies the recursive support tree required to interpret the
concrete do-calculus derivation in every model of the selected class.
-/
structure IdentificationCertificate {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (sourceTerm : ProbabilityTerm S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : DoCalculusDerivation G sourceTerm formula
  supported : forall model : ExactModel S, (member : C.Mem model) ->
    forall assignment, sourceTerm.SupportedAt model assignment ->
      LocalDerivationSupport model assignment derivation

/--
The corresponding pre-compilation certificate: its derivation is expressed
with active-path side conditions and is compiled only after d-separation
correctness has been supplied explicitly.
-/
structure PublishedIdentificationCertificate {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (correct : DSeparationCorrectness G) (sourceTerm : ProbabilityTerm S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  derivation : PathDoCalculusDerivation G sourceTerm formula
  supported : forall model : ExactModel S, (member : C.Mem model) ->
    forall assignment, sourceTerm.SupportedAt model assignment ->
      LocalDerivationSupport model assignment (derivation.compile correct)

/-- Compile path-based side conditions into the executable derivation syntax. -/
def PublishedIdentificationCertificate.compile
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {correct : DSeparationCorrectness G} {sourceTerm : ProbabilityTerm S}
    (certificate : PublishedIdentificationCertificate C correct sourceTerm) :
    IdentificationCertificate C sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation.compile correct
  supported := certificate.supported

/-- Restrict a certificate from a larger class to a subclass. -/
def IdentificationCertificate.restrict
    {S : ObservedSignature} {G : ObservedGraph S} {C D : GraphModelClass G}
    {sourceTerm : ProbabilityTerm S}
    (subset : C.Subset D)
    (certificate : IdentificationCertificate D sourceTerm) :
    IdentificationCertificate C sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := fun model member assignment sourceSupported =>
    certificate.supported model (subset model member) assignment sourceSupported

def PublishedIdentificationCertificate.restrict
    {S : ObservedSignature} {G : ObservedGraph S} {C D : GraphModelClass G}
    {correct : DSeparationCorrectness G} {sourceTerm : ProbabilityTerm S}
    (subset : C.Subset D)
    (certificate : PublishedIdentificationCertificate D correct sourceTerm) :
    PublishedIdentificationCertificate C correct sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  derivation := certificate.derivation
  supported := fun model member assignment sourceSupported =>
    certificate.supported model (subset model member) assignment sourceSupported

end Causality
end Thesis
