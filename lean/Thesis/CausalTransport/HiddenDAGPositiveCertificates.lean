import Thesis.Causality.PositiveDerivationSupport
import Thesis.CausalTransport.HiddenDAGSoundness
import Thesis.CausalTransport.Correspondence

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature} {P : FiniteLatentProjection S}

/-!
# Positive identification certificates in arbitrary finite hidden DAGs

An ID/IDC certificate contains an actual action-free formula and an actual
do-calculus derivation on the projected graph.  Its original support field
applies only inside its selected `GraphModelClass`.  A collapsed hidden DAG
need not belong to that class: a hidden common cause can retain three or more
children.  Supplying a false canonical-membership proof would not be a valid
latent-projection argument.

Instead, retain the certificate's syntax and rebuild its recursive support
from native observational positivity.  The source kernels are zero-free, the
derivation preserves that property, and positive support is proved directly
from finite SCM consistency and rational algebra.  The already implemented
native hidden-DAG soundness theorem then interprets the actual derivation.

The result covers positive full models with arbitrary finite hidden and
private-noise sizes, without an external `PublishedLatentProjection` premise.
This module supplies forward certificate interpretation.  Countermodel
lifting and the converse are proved separately in `HiddenDAGCountermodelLift`
and `HiddenDAGCompleteness`; `HiddenDAGCorrespondence` combines the directions.
Models with observational zeros still require their separate local-support
compiler rather than this positivity-based adapter.
-/

namespace FiniteHiddenDAGSCM

/-- Literal observational preservation transfers positivity to the actual
collapsed root model, regardless of how many children each root has. -/
theorem observationallyPositive_to_collapsed {model : FiniteHiddenDAGSCM S P}
    (positive : model.ObservationallyPositive) :
    Thesis.Causality.ObservationallyPositive model.toLatentRootSCM := by
  intro assignment
  rw [model.toLatentRootSCM_observationalDist]
  exact positive assignment

/-- Observationally equal full models share positivity of each original
observed atom.  Only one of a pair must supply the regularity premise. -/
theorem ObservationallyPositive.transfer {left right : FiniteHiddenDAGSCM S P}
    (observational : left.ObservationalAgreement right)
    (positive : left.ObservationallyPositive) : right.ObservationallyPositive := by
  intro assignment
  exact (QProb.equiv_num_pos_iff
    (observational (FiniteProbRecord.singletonEvent assignment))).mp (positive assignment)

end FiniteHiddenDAGSCM

/-- Native recursive support for every kernel-generated derivation in a
positive full hidden model.  The support construction uses no graph-model
membership and no denotational-soundness premise. -/
noncomputable def HiddenDAGLocalDerivationSupport.ofObservationallyPositive
    {G : ObservedGraph S} (model : FiniteHiddenDAGSCM S P)
    (positive : model.ObservationallyPositive)
    {left right : ProbabilityTerm S}
    (derivation : DoCalculusDerivation G left right)
    (zeroFree : left.ZeroFree) (assignment : S.Assignment) :
    HiddenDAGLocalDerivationSupport model assignment derivation :=
  .ofCollapsed (LocalDerivationSupport.ofObservationallyPositive
    model.toLatentRootSCM (FiniteHiddenDAGSCM.observationallyPositive_to_collapsed positive)
    derivation zeroFree assignment)

namespace IdentificationCertificate

/-- Interpret the certificate's displayed formula in the original full
model.  Its class-indexed support field is deliberately not called: the
actual native support tree is reconstructed under the stated positivity. -/
noncomputable def hiddenDAG_denotational_soundAt
    {C : GraphModelClass P.observedGraph} {source : ProbabilityTerm S}
    (certificate : IdentificationCertificate C source)
    (zeroFree : source.ZeroFree) (model : FiniteHiddenDAGSCM S P)
    (positive : model.ObservationallyPositive) (assignment : S.Assignment) :
    model.TermEquivalentAt source certificate.formula assignment :=
  certificate.derivation.hiddenDAG_denotational_soundAt
    (HiddenDAGLocalDerivationSupport.ofObservationallyPositive model positive
      certificate.derivation zeroFree assignment)

/-- The same actual certificate identifies its source between any two
positive observationally equal full models over this projection.  Positivity
of the right model is transferred from the left, not separately assumed. -/
noncomputable def hiddenDAG_identifiableAt
    {C : GraphModelClass P.observedGraph} {source : ProbabilityTerm S}
    (certificate : IdentificationCertificate C source) (zeroFree : source.ZeroFree)
    (left right : FiniteHiddenDAGSCM S P)
    (observational : left.ObservationalAgreement right)
    (positive : left.ObservationallyPositive) (assignment : S.Assignment) :
    ProbabilityResult.Equivalent (left.termDenote source assignment)
      (right.termDenote source assignment) :=
  certificate.derivation.hiddenDAG_identifiableAt left right observational
    certificate.actionFree assignment
    (HiddenDAGLocalDerivationSupport.ofObservationallyPositive left positive
      certificate.derivation zeroFree assignment)
    (HiddenDAGLocalDerivationSupport.ofObservationallyPositive right
      (FiniteHiddenDAGSCM.ObservationallyPositive.transfer observational positive)
      certificate.derivation zeroFree assignment)

end IdentificationCertificate

/-- Joint source terms are kernels, hence already belong to the fragment.
No extra syntactic or canonical-compatibility obligation is left to callers. -/
noncomputable def JointIdentificationCertificate.hiddenDAG_denotational_soundAt
    {C : GraphModelClass P.observedGraph} {query : JointKernelQuery S}
    (certificate : JointIdentificationCertificate C query)
    (model : FiniteHiddenDAGSCM S P) (positive : model.ObservationallyPositive)
    (assignment : S.Assignment) :
    model.TermEquivalentAt query.sourceTerm certificate.formula assignment :=
  certificate.toGeneric.hiddenDAG_denotational_soundAt trivial model positive assignment

/-- Conditional source terms have the same direct adapter.  Positivity
ensures their actual conditioning cylinders are supported everywhere; no
arbitrary value is assigned to a null conditional outside this premise. -/
noncomputable def ConditionalIdentificationCertificate.hiddenDAG_denotational_soundAt
    {C : GraphModelClass P.observedGraph} {query : ConditionalKernelQuery S}
    (certificate : ConditionalIdentificationCertificate C query)
    (model : FiniteHiddenDAGSCM S P) (positive : model.ObservationallyPositive)
    (assignment : S.Assignment) :
    model.TermEquivalentAt query.sourceTerm certificate.formula assignment :=
  certificate.toGeneric.hiddenDAG_denotational_soundAt trivial model positive assignment

end Causality
end Thesis
