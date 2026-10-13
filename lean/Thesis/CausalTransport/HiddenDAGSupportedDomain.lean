import Thesis.CausalTransport.HiddenDAGAdmissibleDomain

namespace Thesis
namespace Causality

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Engine-independent supported observational identification

The papers permit observed zeros but require positive conditioners for every
conditional that is actually considered, together with admissible external
actions and a positive original causal conditioner for conditional targets.
References: https://ftp.cs.ucla.edu/pub/stat_ser/r327.pdf, pp. 2--3, and
https://ftp.cs.ucla.edu/pub/stat_ser/r329.pdf, pp. 2--3.

An observational expression therefore specifies its *own* primitive
used-conditional domain.  These definitions inspect that expression's
syntax-directed tests in each original native record.  They neither inspect
an identification engine nor assume compiler data or a complete support tree.
The action test is explicitly uniform over supported observed-parent contexts;
the original intervened conditioner remains separate from observable tests.

`jointRepresentedOn` and `conditionalRepresentedOn` state that evaluating the
finite observational expression actually computes the requested causal value
on that domain.  Mere agreement on an arbitrarily selected empty model family
is not substituted for a computable observational representation.  The
query-level identification predicates ask for such a representation whose
domain also includes all positive native records.  `PositiveCovered` exposes
that non-vacuity boundary as primitive demand tests, not an assumed positivity
or soundness theorem.  Coverage is proved for every kernel-generated term and
also for the literal zero expression; invalid `0/0` is not made admissible.

The quantifiers range over every original finite hidden-DAG SCM, allowing
observed zeros and arbitrary finite hidden/private-noise sizes.  Positivity
is used only to ensure a candidate's domain cannot discard the established
positive countermodels.  It is not membership of the ambient soundness class.

This is query-level, expression-qualified identification, not a claim about
every externally admissible cell in a fixed observed law.  In particular it
does not promise that one expression's domain contains the domains of all
alternative expressions.  That stronger coverage statement is not inserted
into a definition or inferred from the published used-conditional caveat.
-/

namespace HiddenDAGSupportedDomain

/-- All positive records satisfy the candidate expression's primitive
demand tests at every reference.  This prevents vacuous domains from making
failed graph queries "identified", without restricting applications to
positive laws or restricting the candidate syntax to a particular engine. -/
def PositiveCovered (projection : FiniteLatentProjection S) (term : ProbabilityTerm S) : Prop :=
  forall model : FiniteHiddenDAGSCM S projection, model.ObservationallyPositive →
    forall reference, model.UsedConditionalsAdmissibleAt term reference

/-- Every kernel-generated term has positive coverage by the independent
syntax-directed positivity proof.  Actual zero outcomes in nonpositive
records are not excluded by the syntactic `ZeroFree` premise of this helper. -/
theorem positiveCovered_of_zeroFree (term : ProbabilityTerm S) (zeroFree : term.ZeroFree) :
    PositiveCovered P term :=
  fun _ positive reference => positive.usedConditionalsAdmissibleAt_of_zeroFree term zeroFree reference

/-- The public semantic domain does not prohibit the literal zero
constructor.  This valid constant has no conditional demands at all; only
an invalid denominator such as the one in `0/0` fails coverage. -/
theorem positiveCovered_zero : PositiveCovered P (ProbabilityTerm.zero : ProbabilityTerm S) :=
  fun _ _ _ => trivial

/-- A joint application requires the original primitive action test and
exactly the conditionals demanded by this independently supplied expression.
No engine success equation or support tree is part of the application. -/
def JointAdmissibleAt (model : FiniteHiddenDAGSCM S P) (query : JointKernelQuery S)
    (term : ProbabilityTerm S) (reference : S.Assignment) : Prop :=
  HiddenDAGAdmissibleDomain.JointAdmissibleAt model query reference ∧
    model.UsedConditionalsAdmissibleAt term reference

/-- A conditional application additionally retains its original native
causal conditioner.  Positivity of the displayed observational expression
does not manufacture a value for an unsupported original target. -/
def ConditionalAdmissibleAt (model : FiniteHiddenDAGSCM S P) (query : ConditionalKernelQuery S)
    (term : ProbabilityTerm S) (reference : S.Assignment) : Prop :=
  HiddenDAGAdmissibleDomain.ConditionalAdmissibleAt model query reference ∧
    model.UsedConditionalsAdmissibleAt term reference

/-- An action-free candidate's entire joint application domain is
observable.  This transfers primitive demand tests, not causal support
inferred from an observation-equivalent but unrelated native record. -/
theorem JointAdmissibleAt.transfer {left right : FiniteHiddenDAGSCM S P}
    {query : JointKernelQuery S} {term : ProbabilityTerm S} {reference : S.Assignment}
    (observational : left.ObservationalAgreement right) (actionFree : term.ActionFree)
    (admissible : JointAdmissibleAt left query term reference) : JointAdmissibleAt right query term reference :=
  ⟨HiddenDAGAdmissibleDomain.JointAdmissibleAt.transfer observational admissible.1,
    admissible.2.transfer observational term actionFree reference⟩

/-- Only the observable part of a conditional application transfers.  The
actual right source conditioner is supplied explicitly, never concluded
from common observed laws or from the candidate's displayed denominator. -/
theorem ConditionalAdmissibleAt.transfer {left right : FiniteHiddenDAGSCM S P}
    {query : ConditionalKernelQuery S} {term : ProbabilityTerm S} {reference : S.Assignment}
    (observational : left.ObservationalAgreement right) (actionFree : term.ActionFree)
    (rightSource : right.ConditioningAdmissibleAt query.operationKernel reference)
    (admissible : ConditionalAdmissibleAt left query term reference) : ConditionalAdmissibleAt right query term reference :=
  ⟨⟨FiniteHiddenDAGSCM.ObservationalActionAdmissibleOnParentSupport.transfer observational admissible.1.1,
      rightSource⟩, admissible.2.transfer observational term actionFree reference⟩

/-- Positive coverage supplies the exact candidate's demand tests in every
positive record, in addition to the primitive external action boundary. -/
theorem jointAdmissibleAt_of_positive (query : JointKernelQuery S) (term : ProbabilityTerm S)
    (covered : PositiveCovered P term) {model : FiniteHiddenDAGSCM S P}
    (positive : model.ObservationallyPositive) (reference : S.Assignment) :
    JointAdmissibleAt model query term reference :=
  ⟨HiddenDAGAdmissibleDomain.jointAdmissibleAt_of_positive positive query reference,
    covered model positive reference⟩

/-- Positive candidate coverage and separately proved source positivity put
the full positive native class inside the conditional application domain. -/
theorem conditionalAdmissibleAt_of_positive (query : ConditionalKernelQuery S) (term : ProbabilityTerm S)
    (covered : PositiveCovered P term) {model : FiniteHiddenDAGSCM S P}
    (positive : model.ObservationallyPositive) (reference : S.Assignment) :
    ConditionalAdmissibleAt model query term reference :=
  ⟨HiddenDAGAdmissibleDomain.conditionalAdmissibleAt_of_positive positive query reference,
    covered model positive reference⟩

/-- Semantic joint uniqueness on a fixed, engine-independent used-
conditional domain.  The right record is not selected from a restricted
family, and every jointly admissible reference is compared. -/
def jointIdentifiableOn (projection : FiniteLatentProjection S) (query : JointKernelQuery S)
    (term : ProbabilityTerm S) : Prop :=
  forall left right : FiniteHiddenDAGSCM S projection,
    left.ObservationalAgreement right → forall reference,
    JointAdmissibleAt left query term reference → JointAdmissibleAt right query term reference →
    Nonempty (ProbabilityResult.Equivalent
      (left.kernelDenote query.operationKernel reference) (right.kernelDenote query.operationKernel reference))

/-- Conditional uniqueness is compared only when both original causal
conditioners and the candidate's actual demand tests are admissible. -/
def conditionalIdentifiableOn (projection : FiniteLatentProjection S) (query : ConditionalKernelQuery S)
    (term : ProbabilityTerm S) : Prop :=
  forall left right : FiniteHiddenDAGSCM S projection,
    left.ObservationalAgreement right → forall reference,
    ConditionalAdmissibleAt left query term reference → ConditionalAdmissibleAt right query term reference →
    Nonempty (ProbabilityResult.Equivalent
      (left.kernelDenote query.operationKernel reference) (right.kernelDenote query.operationKernel reference))

/-- The candidate observational expression actually computes the joint
query at every application in its primitive demand domain.  No graph
derivation, compiler tree or identification outcome is a premise. -/
def jointRepresentedOn (projection : FiniteLatentProjection S) (query : JointKernelQuery S)
    (term : ProbabilityTerm S) : Prop :=
  forall model : FiniteHiddenDAGSCM S projection, forall reference,
    JointAdmissibleAt model query term reference →
    Nonempty (model.TermEquivalentAt query.sourceTerm term reference)

/-- The conditional representation retains the actual target's support
qualification, with no value assigned to null original conditioners. -/
def conditionalRepresentedOn (projection : FiniteLatentProjection S) (query : ConditionalKernelQuery S)
    (term : ProbabilityTerm S) : Prop :=
  forall model : FiniteHiddenDAGSCM S projection, forall reference,
    ConditionalAdmissibleAt model query term reference →
    Nonempty (model.TermEquivalentAt query.sourceTerm term reference)

/-- Query-level supported observational identification: an actual finite
action-free expression computes the query on its explicit used-conditional
domain, and that domain includes every positive native record.  Neither
structural success nor the engine's selected formula occurs here. -/
def jointIdentifiable (projection : FiniteLatentProjection S) (query : JointKernelQuery S) : Prop :=
  ∃ term : ProbabilityTerm S, term.ActionFree ∧ PositiveCovered projection term ∧
    jointRepresentedOn projection query term

/-- The same independently specified existence predicate for conditional
queries.  It quantifies over observational expressions and all original
finite models, not over an assumed imported theorem family. -/
def conditionalIdentifiable (projection : FiniteLatentProjection S) (query : ConditionalKernelQuery S) : Prop :=
  ∃ term : ProbabilityTerm S, term.ActionFree ∧ PositiveCovered projection term ∧
    conditionalRepresentedOn projection query term

/-- A genuine observational representation gives semantic uniqueness by
its two native evaluations and observational invariance of the candidate.
The witnesses are eliminated only into the proposition `Nonempty`, not
selected into executable data by choice. -/
theorem jointRepresentedOn_identifiableOn (query : JointKernelQuery S) (term : ProbabilityTerm S)
    (actionFree : term.ActionFree) (represented : jointRepresentedOn P query term) :
    jointIdentifiableOn P query term := by
  intro left right observational reference leftAdmissible rightAdmissible
  rcases represented left reference leftAdmissible with ⟨leftSound⟩
  rcases represented right reference rightAdmissible with ⟨rightSound⟩
  exact ⟨ProbabilityResult.trans leftSound
    (ProbabilityResult.trans (FiniteHiddenDAGSCM.actionFree_invariant left right observational term actionFree reference)
      (ProbabilityResult.symm rightSound))⟩

/-- Conditional representation gives the original target's value equality
on the separately retained common-source domain. -/
theorem conditionalRepresentedOn_identifiableOn (query : ConditionalKernelQuery S) (term : ProbabilityTerm S)
    (actionFree : term.ActionFree) (represented : conditionalRepresentedOn P query term) :
    conditionalIdentifiableOn P query term := by
  intro left right observational reference leftAdmissible rightAdmissible
  rcases represented left reference leftAdmissible with ⟨leftSound⟩
  rcases represented right reference rightAdmissible with ⟨rightSound⟩
  exact ⟨ProbabilityResult.trans leftSound
    (ProbabilityResult.trans (FiniteHiddenDAGSCM.actionFree_invariant left right observational term actionFree reference)
      (ProbabilityResult.symm rightSound))⟩

/-- Semantic uniqueness on any positive-covered candidate domain includes
the full positive native model class.  This restriction is solely the
countermodel/completeness direction, never the zero-containing soundness
domain of the candidate representation. -/
theorem jointIdentifiableOn_positive (query : JointKernelQuery S) (term : ProbabilityTerm S)
    (covered : PositiveCovered P term) (identified : jointIdentifiableOn P query term) :
    (HiddenDAGModelClass.positive P).identifiable query := by
  intro left right leftPositive rightPositive observational reference
  exact identified left right observational reference
    (jointAdmissibleAt_of_positive query term covered leftPositive reference)
    (jointAdmissibleAt_of_positive query term covered rightPositive reference)

/-- The analogous restriction preserves the positive class's old
common-support relation and the unchanged original conditional query. -/
theorem conditionalIdentifiableOn_positive (query : ConditionalKernelQuery S) (term : ProbabilityTerm S)
    (covered : PositiveCovered P term) (identified : conditionalIdentifiableOn P query term) :
    (HiddenDAGModelClass.positive P).conditionalIdentifiable query := by
  intro left right leftPositive rightPositive observational reference _leftSupport _rightSupport
  exact identified left right observational reference
    (conditionalAdmissibleAt_of_positive query term covered leftPositive reference)
    (conditionalAdmissibleAt_of_positive query term covered rightPositive reference)

/-- A supported observational representation cannot discard the positive
joint countermodels.  Unpacking its existential is proof-only; the future
compiler must read its own outcome to construct a formula in `Type`. -/
theorem jointIdentifiable_positive (query : JointKernelQuery S) (identified : jointIdentifiable P query) :
    (HiddenDAGModelClass.positive P).identifiable query := by
  rcases identified with ⟨term, actionFree, covered, represented⟩
  exact jointIdentifiableOn_positive query term covered
    (jointRepresentedOn_identifiableOn query term actionFree represented)

/-- Supported conditional identification likewise restricts to the whole
positive native class without choice or a semantic excluded-middle split. -/
theorem conditionalIdentifiable_positive (query : ConditionalKernelQuery S) (identified : conditionalIdentifiable P query) :
    (HiddenDAGModelClass.positive P).conditionalIdentifiable query := by
  rcases identified with ⟨term, actionFree, covered, represented⟩
  exact conditionalIdentifiableOn_positive query term covered
    (conditionalRepresentedOn_identifiableOn query term actionFree represented)

end HiddenDAGSupportedDomain

/-- Every positive native joint counterpair lies in every positive-covered
candidate domain, at every reference.  This proves actual coverage of the
exhibited records rather than redefining failure as lack of a formula. -/
theorem HiddenDAGCounterexampleIn.supported_left_admissible {query : JointKernelQuery S}
    (pair : HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive P) query)
    (term : ProbabilityTerm S) (covered : HiddenDAGSupportedDomain.PositiveCovered P term) (reference : S.Assignment) :
    HiddenDAGSupportedDomain.JointAdmissibleAt pair.left query term reference :=
  HiddenDAGSupportedDomain.jointAdmissibleAt_of_positive query term covered pair.left_mem reference

theorem HiddenDAGCounterexampleIn.supported_right_admissible {query : JointKernelQuery S}
    (pair : HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive P) query)
    (term : ProbabilityTerm S) (covered : HiddenDAGSupportedDomain.PositiveCovered P term) (reference : S.Assignment) :
    HiddenDAGSupportedDomain.JointAdmissibleAt pair.right query term reference :=
  HiddenDAGSupportedDomain.jointAdmissibleAt_of_positive query term covered pair.right_mem reference

/-- Positive conditional countermodels also meet the original native
conditioner test, so missing common support cannot explain the failure. -/
theorem HiddenDAGConditionalCounterexampleIn.supported_left_admissible {query : ConditionalKernelQuery S}
    (pair : HiddenDAGConditionalCounterexampleIn (HiddenDAGModelClass.positive P) query)
    (term : ProbabilityTerm S) (covered : HiddenDAGSupportedDomain.PositiveCovered P term) (reference : S.Assignment) :
    HiddenDAGSupportedDomain.ConditionalAdmissibleAt pair.left query term reference :=
  HiddenDAGSupportedDomain.conditionalAdmissibleAt_of_positive query term covered pair.left_mem reference

theorem HiddenDAGConditionalCounterexampleIn.supported_right_admissible {query : ConditionalKernelQuery S}
    (pair : HiddenDAGConditionalCounterexampleIn (HiddenDAGModelClass.positive P) query)
    (term : ProbabilityTerm S) (covered : HiddenDAGSupportedDomain.PositiveCovered P term) (reference : S.Assignment) :
    HiddenDAGSupportedDomain.ConditionalAdmissibleAt pair.right query term reference :=
  HiddenDAGSupportedDomain.conditionalAdmissibleAt_of_positive query term covered pair.right_mem reference

/-- Genuine joint separation refutes any supported observational
representation with positive coverage.  No particular candidate expression
or separating reference is selected to construct the countermodel. -/
theorem HiddenDAGCounterexampleIn.not_supported_identifiable {query : JointKernelQuery S}
    (pair : HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive P) query) :
    Not (HiddenDAGSupportedDomain.jointIdentifiable P query) :=
  fun identified => pair.not_identifiable (HiddenDAGSupportedDomain.jointIdentifiable_positive query identified)

/-- Conditional countermodel separation on genuine common support refutes
the corresponding supported observational representation predicate. -/
theorem HiddenDAGConditionalCounterexampleIn.not_supported_identifiable {query : ConditionalKernelQuery S}
    (pair : HiddenDAGConditionalCounterexampleIn (HiddenDAGModelClass.positive P) query) :
    Not (HiddenDAGSupportedDomain.conditionalIdentifiable P query) :=
  fun identified => pair.not_identifiable (HiddenDAGSupportedDomain.conditionalIdentifiable_positive query identified)

end Causality
end Thesis
