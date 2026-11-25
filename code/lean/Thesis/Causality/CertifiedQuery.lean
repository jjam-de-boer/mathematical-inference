import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ObservationalEvaluation

namespace Thesis.Causality.CertifiedQuery
open Probability

/-!
# Class-indexed evidence for a numerical causal answer

A graph program may produce an observational expression, but that expression
is not by itself evidence that a numerical answer is valid for the record
being read.  This module makes the missing application boundary explicit.
Every formula or bound names its source query, its class of generative SCMs,
and its assignment-local domain.  Applying it requires actual membership
and domain data.  Thus a caller cannot turn an arbitrary formula, an empty
model class, or an unproved pair of endpoints into an accepted answer.

The domain lives in `Type`: support witnesses retain the displayed rational
value and are constructed by inspecting the finite computation.  No choice
of a witness from a mere existence proposition is needed.  Domains may
express additional mechanism restrictions or local support, but those
restrictions remain visible parts of the certificate.  In particular,
conditioning a mode's belief does not silently change the class of models
for which a population-identification certificate was proved.

Certificates are independent of any particular identification engine.  The
transport layer supplies adapters from the existing do-calculus proofs;
specialized model classes may instead prove their own observational formula.
All equalities use the existing partial-result semantics: undefined agrees
only with undefined, and a supported zero remains a genuine numerical value.
-/

variable {S : ObservedSignature.{0}}

/-- A formula valid for `source` throughout an explicitly named class and
on an explicit local application domain.  `actionFree` licenses reading
the formula from the observational law rather than the hidden mechanisms. -/
structure FormulaCertificate (source : ProbabilityTerm S) where
  models : ExactModel S → Prop
  domain : (model : ExactModel S) → S.Assignment → Type
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  sound : ∀ model, models model → ∀ reference, domain model reference →
    ProbabilityTerm.EquivalentAt model source formula reference

namespace FormulaCertificate

/-- A certificate together with evidence that this particular model and
reference lie inside its stated scope.  Empty classes therefore cannot be
used to manufacture an answer about a model outside the class. -/
structure At (source : ProbabilityTerm S) (model : ExactModel S)
    (reference : S.Assignment) where
  certificate : FormulaCertificate source
  member : certificate.models model
  application : certificate.domain model reference

/-- Read only the observational table of the admitted generative model.
The result remains partial so an undefined expression is never completed. -/
def At.value {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} (answer : At source model reference) :
    ProbabilityResult.Result :=
  answer.certificate.formula.observationalDenote model.observationalDist reference

/-- Numerical correctness of an applied certificate.  The first step is
its class-wide theorem; the second is the intrinsic action-free evaluation
lemma, which justifies replacing SCM interpretation by the observed table. -/
noncomputable def At.correct {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} (answer : At source model reference) :
    ProbabilityResult.Equivalent (source.denote model reference) answer.value := by
  have agreement := answer.certificate.sound model answer.member reference answer.application
  have observed := ProbabilityTerm.observationalDenote_eq_scm model
    answer.certificate.formula answer.certificate.actionFree reference
  unfold At.value
  rw [observed]
  exact agreement

end FormulaCertificate

/-- A class-wide enclosure for the same source query.  The bound theorem
quantifies over every supported value, so it is independent of the choice
of unreduced rational presentation.  Endpoints are not trusted input data. -/
structure BoundsCertificate (source : ProbabilityTerm S) where
  models : ExactModel S → Prop
  domain : (model : ExactModel S) → S.Assignment → Type
  lower : QProb
  upper : QProb
  valid : ∀ model, models model → ∀ reference, domain model reference →
    ∀ value, ProbabilityResult.Equivalent (source.denote model reference) (some value) →
      QProb.LE lower value ∧ QProb.LE value upper

namespace BoundsCertificate

/-- Applying bounds requires both class/domain membership and a defined
target.  An unsupported conditioner cannot be enclosed by invented numbers. -/
structure At (source : ProbabilityTerm S) (model : ExactModel S)
    (reference : S.Assignment) where
  certificate : BoundsCertificate source
  member : certificate.models model
  application : certificate.domain model reference
  supported : source.SupportedAt model reference

/-- The actual supported source value lies between the certified endpoints.
This is the evidence carried alongside the displayed interval. -/
theorem At.correct {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} (answer : At source model reference) :
    QProb.LE answer.certificate.lower answer.supported.1 ∧
      QProb.LE answer.supported.1 answer.certificate.upper :=
  answer.certificate.valid model answer.member reference answer.application
    answer.supported.1 answer.supported.2

end BoundsCertificate

/-- A certified public answer keeps its query, model and reference as type
indices.  Diagnostic outcomes carry no numerical assertion.  `identified`
retains the whole formula certificate, including its class and local domain;
`bounded` retains its bound proof.  Display projections may discard those
proofs, but they are never an alternative constructor for a certified answer. -/
inductive Answer (source : ProbabilityTerm S) (model : ExactModel S)
    (reference : S.Assignment) where
  | identified (evidence : FormulaCertificate.At source model reference)
  | bounded (evidence : BoundsCertificate.At source model reference)
  | undefined
  | failed (failure : IdentificationFail S)
  | unfinished
  | modeUnsupported

namespace Answer

/-- Recognize a certified formula branch without erasing the certificate
from the answer itself. Diagnostic and interval branches are kept distinct. -/
def isIdentified {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} : Answer source model reference → Bool
  | .identified _ => true
  | _ => false

/-- Read the numerical component only from a class-certified formula. An
undefined expression remains `none`, independently of its graph provenance. -/
def identifiedValue {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} : Answer source model reference → Option QProb
  | .identified evidence => evidence.value
  | _ => none

/-- A declared experimental-access miss makes no assertion about whether
the same query is graphically identifiable in some other epistemic policy. -/
def isModeUnsupported {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} : Answer source model reference → Bool
  | .modeUnsupported => true
  | _ => false

end Answer

end Thesis.Causality.CertifiedQuery
