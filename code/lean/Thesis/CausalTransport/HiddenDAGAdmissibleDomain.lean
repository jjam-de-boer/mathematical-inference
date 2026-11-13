import Thesis.CausalTransport.HiddenDAGAdmissibility
import Thesis.CausalTransport.HiddenDAGModelClass

namespace Thesis
namespace Causality

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# The primitive admissible-query domain in original finite hidden DAGs

The domain below is stated before, and independently of, any identification
engine or returned expression.  A joint application fixes action values and
requires their overlap on every supported observed-parent context.  A
conditional application additionally requires a positive original intervened
conditioner.  The parent-context quantification is explicit: these definitions
do not silently replace it by a pointwise test at one context.

Identifiability compares every pair of actual SCM records on the original
DAG at references where both queries meet those primitive conditions.  The
records may have observed zeros and arbitrary finite hidden/noise alphabets.
No membership in a selected model family, compiler data, derivation support
or computed program result is part of this semantic premise.

These are the *primitive query* conditions, not a claim that all conditionals
in every identifying expression are automatically admissible.  Used-
conditional tests remain a separate boundary of a formula's application.
Consequently this module supports a genuine one-way completeness theorem:
semantic identifiability on this domain forces structural success, whose
certificate can then be applied wherever its used conditionals are admissible.
It does not assert an unrestricted success iff identifiability theorem.

Positive records lie in this reference-indexed domain everywhere.  The
countermodel conversions below therefore retain the existing positive
records while certifying their actual admissible applications explicitly.
They do not weaken the ambient semantic domain to positive records, or
choose a separating reference from propositional non-identifiability.
-/

namespace HiddenDAGAdmissibleDomain

/-- The primitive joint-query boundary, expressed on the actual original
DAG.  The outcome may have probability zero, and unrelated observed atoms
may be zero.  No proposed identifying formula occurs in the definition. -/
def JointAdmissibleAt (model : FiniteHiddenDAGSCM S P)
    (query : JointKernelQuery S) (reference : S.Assignment) : Prop :=
  model.ObservationalActionAdmissibleOnParentSupport query.action reference

/-- The original conditional target must be meaningful in addition to the
joint action boundary.  Positivity is required of its actual intervened
conditioner, not its outcome and not an observational replacement. -/
def ConditionalAdmissibleAt (model : FiniteHiddenDAGSCM S P)
    (query : ConditionalKernelQuery S) (reference : S.Assignment) : Prop :=
  model.ObservationalActionAdmissibleOnParentSupport query.action reference ∧
    model.ConditioningAdmissibleAt query.operationKernel reference

/-- Primitive-domain joint identification quantifies over all actual native
model pairs.  Agreement is requested at every jointly admissible reference;
it is not restricted to references selected after an engine succeeds. -/
def jointIdentifiable (projection : FiniteLatentProjection S) (query : JointKernelQuery S) : Prop :=
  forall left right : FiniteHiddenDAGSCM S projection,
    left.ObservationalAgreement right → forall reference : S.Assignment,
    JointAdmissibleAt left query reference → JointAdmissibleAt right query reference →
    Nonempty (ProbabilityResult.Equivalent
      (left.kernelDenote query.operationKernel reference) (right.kernelDenote query.operationKernel reference))

/-- Conditional comparison retains positive original conditioners in both
records.  Observational agreement does not by itself transfer that causal
positivity; neither unsupported conditionals nor support-domain mismatches
can stand in for a disagreement of genuinely defined conditional values. -/
def conditionalIdentifiable (projection : FiniteLatentProjection S) (query : ConditionalKernelQuery S) : Prop :=
  forall left right : FiniteHiddenDAGSCM S projection,
    left.ObservationalAgreement right → forall reference : S.Assignment,
    ConditionalAdmissibleAt left query reference → ConditionalAdmissibleAt right query reference →
    Nonempty (ProbabilityResult.Equivalent
      (left.kernelDenote query.operationKernel reference) (right.kernelDenote query.operationKernel reference))

/-- Primitive joint admissibility is observable.  This convenience theorem
does not supply the separate used-conditional tests for an arbitrary formula. -/
theorem JointAdmissibleAt.transfer {left right : FiniteHiddenDAGSCM S P}
    {query : JointKernelQuery S} {reference : S.Assignment}
    (observational : left.ObservationalAgreement right)
    (admissible : JointAdmissibleAt left query reference) : JointAdmissibleAt right query reference :=
  FiniteHiddenDAGSCM.ObservationalActionAdmissibleOnParentSupport.transfer observational admissible

/-- Positive observed laws supply every supported-parent action context,
not just one chosen reference.  The proof uses the primitive positivity
construction; it imports neither identification soundness nor an engine. -/
theorem jointAdmissibleAt_of_positive {model : FiniteHiddenDAGSCM S P}
    (positive : model.ObservationallyPositive) (query : JointKernelQuery S) (reference : S.Assignment) :
    JointAdmissibleAt model query reference :=
  positive.actionAdmissibleOnParentSupport query.action reference

/-- Positive records also have the actual original causal conditioner at
every reference.  This source positivity is constructed separately rather
than inferred from two-model observational agreement. -/
theorem conditionalAdmissibleAt_of_positive {model : FiniteHiddenDAGSCM S P}
    (positive : model.ObservationallyPositive) (query : ConditionalKernelQuery S) (reference : S.Assignment) :
    ConditionalAdmissibleAt model query reference :=
  ⟨positive.actionAdmissibleOnParentSupport query.action reference,
    positive.conditioningAdmissibleAt query.operationKernel reference⟩

/-- Identification on the primitive zero-containing domain includes the
entire positive native class.  This restriction is used only in the
completeness/countermodel direction, not to restrict soundness to positives. -/
theorem jointIdentifiable_positive (query : JointKernelQuery S)
    (identified : jointIdentifiable P query) : (HiddenDAGModelClass.positive P).identifiable query := by
  intro left right leftPositive rightPositive observational reference
  exact identified left right observational reference
    (jointAdmissibleAt_of_positive leftPositive query reference)
    (jointAdmissibleAt_of_positive rightPositive query reference)

/-- The conditional restriction preserves the old common-support relation.
Positive membership constructs the primitive target conditions; no rational
representative or model is selected from an existential proposition. -/
theorem conditionalIdentifiable_positive (query : ConditionalKernelQuery S)
    (identified : conditionalIdentifiable P query) :
    (HiddenDAGModelClass.positive P).conditionalIdentifiable query := by
  intro left right leftPositive rightPositive observational reference _leftSupport _rightSupport
  exact identified left right observational reference
    (conditionalAdmissibleAt_of_positive leftPositive query reference)
    (conditionalAdmissibleAt_of_positive rightPositive query reference)

end HiddenDAGAdmissibleDomain

/-- Actual original-DAG records separating a joint query while satisfying
its primitive action domain at every reference.  This strong admissibility
field avoids selecting a particular separating reference by choice. -/
structure HiddenDAGAdmissibleJointCounterexample (projection : FiniteLatentProjection S) (query : JointKernelQuery S) where
  left : FiniteHiddenDAGSCM S projection
  right : FiniteHiddenDAGSCM S projection
  observationally_equal : left.ObservationalAgreement right
  left_admissible : forall reference, HiddenDAGAdmissibleDomain.JointAdmissibleAt left query reference
  right_admissible : forall reference, HiddenDAGAdmissibleDomain.JointAdmissibleAt right query reference
  query_separated : Not (left.KernelResultEquivalent right query.operationKernel)

/-- Conditional separation remains on common support of the unchanged
query.  Both records also satisfy its original conditioner and action tests
everywhere, so an inadmissible action or null target cannot explain failure. -/
structure HiddenDAGAdmissibleConditionalCounterexample (projection : FiniteLatentProjection S)
    (query : ConditionalKernelQuery S) where
  left : FiniteHiddenDAGSCM S projection
  right : FiniteHiddenDAGSCM S projection
  observationally_equal : left.ObservationalAgreement right
  left_admissible : forall reference, HiddenDAGAdmissibleDomain.ConditionalAdmissibleAt left query reference
  right_admissible : forall reference, HiddenDAGAdmissibleDomain.ConditionalAdmissibleAt right query reference
  query_separated : Not (left.KernelAgreesOnCommonSupport right query.operationKernel)

/-- Keep the two exhibited records, observed-law equality and original
query separation literally unchanged.  Independently proved positive
coverage supplies their primitive-domain application witnesses. -/
noncomputable def HiddenDAGCounterexampleIn.toAdmissible {query : JointKernelQuery S}
    (pair : HiddenDAGCounterexampleIn (HiddenDAGModelClass.positive P) query) :
    HiddenDAGAdmissibleJointCounterexample P query where
  left := pair.left
  right := pair.right
  observationally_equal := pair.observationally_equal
  left_admissible := HiddenDAGAdmissibleDomain.jointAdmissibleAt_of_positive pair.left_mem query
  right_admissible := HiddenDAGAdmissibleDomain.jointAdmissibleAt_of_positive pair.right_mem query
  query_separated := pair.query_separated

/-- The analogous conversion retains genuine conditional common-support
value separation and proves the target's causal positivity in both records.
No soundness theorem is used to establish countermodel admissibility. -/
noncomputable def HiddenDAGConditionalCounterexampleIn.toAdmissible {query : ConditionalKernelQuery S}
    (pair : HiddenDAGConditionalCounterexampleIn (HiddenDAGModelClass.positive P) query) :
    HiddenDAGAdmissibleConditionalCounterexample P query where
  left := pair.left
  right := pair.right
  observationally_equal := pair.observationally_equal
  left_admissible := HiddenDAGAdmissibleDomain.conditionalAdmissibleAt_of_positive pair.left_mem query
  right_admissible := HiddenDAGAdmissibleDomain.conditionalAdmissibleAt_of_positive pair.right_mem query
  query_separated := pair.query_separated

/-- An actual admissible pair contradicts primitive-domain joint
identification by assembling the full reference-wise agreement.  No
excluded-middle split on the semantic premise or separating-reference
selection is introduced. -/
theorem HiddenDAGAdmissibleJointCounterexample.not_identifiable {query : JointKernelQuery S}
    (pair : HiddenDAGAdmissibleJointCounterexample P query) :
    Not (HiddenDAGAdmissibleDomain.jointIdentifiable P query) := by
  intro identified
  apply pair.query_separated
  intro reference
  exact identified pair.left pair.right pair.observationally_equal reference
    (pair.left_admissible reference) (pair.right_admissible reference)

/-- Genuine common-support disagreement refutes primitive-domain
conditional identification.  The supplied source-support witnesses are not
used to manufacture an undefined conditional or complete division by zero. -/
theorem HiddenDAGAdmissibleConditionalCounterexample.not_identifiable {query : ConditionalKernelQuery S}
    (pair : HiddenDAGAdmissibleConditionalCounterexample P query) :
    Not (HiddenDAGAdmissibleDomain.conditionalIdentifiable P query) := by
  intro identified
  apply pair.query_separated
  intro reference _leftSupport _rightSupport
  exact identified pair.left pair.right pair.observationally_equal reference
    (pair.left_admissible reference) (pair.right_admissible reference)

end Causality
end Thesis
