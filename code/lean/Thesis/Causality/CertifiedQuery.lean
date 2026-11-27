import Thesis.Causality.IdentificationKernel
import Thesis.Causality.ObservationalEvaluation

namespace Thesis.Causality.CertifiedQuery
open Probability

/-!
# Class-indexed evidence for a numerical causal answer

A graph program may produce an observational expression, but that expression
is not by itself evidence that a numerical answer is valid for the record
being read.  This module makes the missing application boundary explicit.
The model class is a type index supplied by the consumer of the proof.
Formula soundness ranges over every member where the source and the printed
observational formula are defined. An optional replacement must additionally
prove that its formula is defined everywhere the source is supported.
Bounds cover every supported source value in the class. An answer cannot
supply a private model class or an answer-dependent domain to narrow either
obligation.

Certificates are independent of any particular identification engine.  The
transport layer supplies adapters from the existing do-calculus proofs;
specialized model classes may instead prove their own observational formula.
All equalities use the existing partial-result semantics: undefined agrees
only with undefined, and a supported zero remains a genuine numerical value.
-/

variable {S : ObservedSignature.{0}}

/-- An observational formula valid throughout the declared class on the
common support of the source query and the formula's used conditionals. -/
structure FormulaCertificate (source : ProbabilityTerm S) (models : ExactModel S → Prop) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  sound : ∀ model, models model → ∀ reference,
    source.SupportedAt model reference → formula.SupportedAt model reference →
      ProbabilityTerm.EquivalentAt model source formula reference

namespace FormulaCertificate

/-- A replacement covers the query's full supported domain in the class.
Its own formula's support cannot select which source instances it certifies. -/
structure Total (source : ProbabilityTerm S) (models : ExactModel S → Prop) where
  certificate : FormulaCertificate source models
  defined : ∀ model, models model → ∀ reference, source.SupportedAt model reference →
    certificate.formula.SupportedAt model reference

/-- Applying a formula requires class membership and both support witnesses.
These checks keep an undefined conditioner out of the identified branch. -/
structure At (source : ProbabilityTerm S) (model : ExactModel S)
    (reference : S.Assignment)
    (models : ExactModel S → Prop := fun candidate => HasProjectedGraph candidate model.observedGraph)
    where
  certificate : FormulaCertificate source models
  member : models model
  sourceSupported : source.SupportedAt model reference
  formulaSupported : certificate.formula.SupportedAt model reference

/-- Read only the observational table of the admitted generative model.
The result remains partial so an undefined expression is never completed. -/
def At.value {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} {models : ExactModel S → Prop}
    (answer : At source model reference models) :
    ProbabilityResult.Result :=
  answer.certificate.formula.observationalDenote model.observationalDist reference

/-- Numerical correctness of an applied certificate.  The first step is
its class-wide theorem; the second is the intrinsic action-free evaluation
lemma, which justifies replacing SCM interpretation by the observed table. -/
noncomputable def At.correct {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} {models : ExactModel S → Prop}
    (answer : At source model reference models) :
    ProbabilityResult.Equivalent (source.denote model reference) answer.value := by
  have agreement := answer.certificate.sound model answer.member reference
    answer.sourceSupported answer.formulaSupported
  have observed := ProbabilityTerm.observationalDenote_eq_scm model
    answer.certificate.formula answer.certificate.actionFree reference
  unfold At.value
  rw [observed]
  exact agreement

end FormulaCertificate

/-- A class-wide enclosure for the same source query.  The bound theorem
quantifies over every supported value, so it is independent of the choice
of unreduced rational presentation.  Endpoints are not trusted input data. -/
structure BoundsCertificate (source : ProbabilityTerm S) (models : ExactModel S → Prop) where
  lower : QProb
  upper : QProb
  valid : ∀ model, models model → ∀ reference,
    ∀ value, ProbabilityResult.Equivalent (source.denote model reference) (some value) →
      QProb.LE lower value ∧ QProb.LE value upper

namespace BoundsCertificate

/-- Applying bounds requires class membership and a defined
target.  An unsupported conditioner cannot be enclosed by invented numbers. -/
structure At (source : ProbabilityTerm S) (model : ExactModel S)
    (reference : S.Assignment)
    (models : ExactModel S → Prop := fun candidate => HasProjectedGraph candidate model.observedGraph)
    where
  certificate : BoundsCertificate source models
  member : models model
  supported : source.SupportedAt model reference

/-- The actual supported source value lies between the certified endpoints.
This is the evidence carried alongside the displayed interval. -/
theorem At.correct {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} {models : ExactModel S → Prop}
    (answer : At source model reference models) :
    QProb.LE answer.certificate.lower answer.supported.1 ∧
      QProb.LE answer.supported.1 answer.certificate.upper :=
  answer.certificate.valid model answer.member reference
    answer.supported.1 answer.supported.2

end BoundsCertificate

/-- A certified public answer keeps its query, model, reference and model class
as type indices.  Diagnostic outcomes carry no numerical assertion.  `identified`
retains the whole formula certificate, including its class and local domain;
`bounded` retains its bound proof.  Display projections may discard those
proofs, but they are never an alternative constructor for a certified answer. -/
inductive Answer (source : ProbabilityTerm S) (model : ExactModel S)
    (reference : S.Assignment)
    (models : ExactModel S → Prop := fun candidate => HasProjectedGraph candidate model.observedGraph)
    where
  | identified (evidence : FormulaCertificate.At source model reference models)
  | bounded (evidence : BoundsCertificate.At source model reference models)
  | undefined
  | failed (failure : IdentificationFail S)
  | unfinished
  | modeUnsupported

namespace Answer

/-- Recognize a certified formula branch without erasing the certificate
from the answer itself. Diagnostic and interval branches are kept distinct. -/
def isIdentified {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} {models : ExactModel S → Prop} :
    Answer source model reference models → Bool
  | .identified _ => true
  | _ => false

/-- Read the numerical component only from a class-certified formula. An
undefined expression remains `none`, independently of its graph provenance. -/
def identifiedValue {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} {models : ExactModel S → Prop} :
    Answer source model reference models → Option QProb
  | .identified evidence => evidence.value
  | _ => none

/-- A declared experimental-access miss makes no assertion about whether
the same query is graphically identifiable in some other epistemic policy. -/
def isModeUnsupported {source : ProbabilityTerm S} {model : ExactModel S}
    {reference : S.Assignment} {models : ExactModel S → Prop} :
    Answer source model reference models → Bool
  | .modeUnsupported => true
  | _ => false

end Answer

end Thesis.Causality.CertifiedQuery
