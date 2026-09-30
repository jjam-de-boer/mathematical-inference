import Thesis.CausalTransport.HedgeOutcomeFlow
import Thesis.CausalTransport.HedgePositive
import Thesis.CausalTransport.KernelSuccessCompilation

namespace Thesis
namespace Causality

open Probability

/-!
# Assembly lemmas for the published completeness theorem

`Completeness` and `Soundness` remain independent implementation modules.
`HedgeOutcomeFlow` develops its countermodel semantics without importing
soundness; `HedgePositive` uses the finite marginalization algebra from
`Soundness` at a one-way integration boundary.  This module is a further
assembly boundary: it may use `ObservedGraph.publishedSoundness` to connect
an inspectable derivation with its denotation, but neither main theorem
development imports this file.

The first application is conditional identification.  Bayes compilation
needs a strictly positive identified denominator only at assignments where
the source conditional kernel is defined.  Earlier constructors asked for
positivity at *every* assignment, which is stronger than the certificate
interface and is false for general interventional denominators.  The lemmas
below extract the exact local positivity fact from source support, transport
it through the identified denominator using published soundness, and package
arbitrary numerator and denominator certificates without imposing a special
syntactic shape on either formula.

The replacement engine's full structural success compiler is now available
independently in `KernelSuccessCompilation`.  At this integration boundary,
published soundness turns its supported certificate into correctness and
identifiability of every identified joint result.  These conclusions do not
assert that every semantically identifiable query succeeds; that direction
still requires the failure/hedge countermodel argument.
-/

/-! ## Denotational correctness of every successful replacement joint run -/

/-- Every identified replacement-engine formula denotes the requested joint
kernel, in every member of an observationally positive compatible model class
and at every assignment.  The success compiler constructs the derivation;
completed published soundness is used only here to interpret it. -/
noncomputable def identifyJointKernel_identified_soundAt
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyJointKernel G query = .identified term)
    (model : ExactModel S) (member : C.Mem model) (assignment : S.Assignment) :
    ProbabilityTerm.EquivalentAt model query.sourceTerm term assignment :=
  let certificate := identifyJointKernelPublishedCertificate correct obsPositive query result
  certificate.compile.denotational_soundAt G.publishedSoundness model member assignment
    (query.supportedAt model assignment)

/-- An identified replacement-engine result proves semantic identifiability
in the selected positive class.  This is the algorithm's success-to-semantics
direction, not an assumed completeness interface or a guarantee of success
for every identifiable query. -/
theorem identifyJointKernel_identified_identifiable
    {S : ObservedSignature.{0}} {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (obsPositive : forall {model}, C.Mem model -> ObservationallyPositive model)
    (query : JointKernelQuery S) {term : ProbabilityTerm S}
    (result : identifyJointKernel G query = .identified term) : C.identifiable query :=
  JointIdentificationCertificate.identifiable G.publishedSoundness
    (identifyJointKernelPublishedCertificate correct obsPositive query result).compile

/-! ## Support-sensitive Bayes assembly

`ProbabilityResult.PositiveSupportedValue` and the primitive denominator
support extractor live in `Causality.Semantics`: they can be reused by the
current-kernel compiler without importing this soundness-dependent assembly
boundary.  The lemmas below perform the genuinely graph-indexed transport.
-/

/--
At a supported conditional-query assignment, the formula returned by an
arbitrary certificate for the Bayes denominator has positive numerator.

Source support makes the literal quotient
`P(Y,Z | do(X)) / P(Z | do(X))` defined, hence exposes a positive value for
`P(Z | do(X))`.  Published soundness identifies that literal denominator
with the certificate formula.  Positivity is invariant under rational
cross-multiplication, so no assumption about the formula's syntax is needed.
-/
noncomputable def PublishedJointCertificate.denominatorFormulaPositiveAt
    {S : ObservedSignature} {G : ObservedGraph S}
    {C : GraphModelClass G} (sound : PublishedSoundness S G)
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (denominator : PublishedJointCertificate C correct q.jointDenominator)
    (model : ExactModel S) (member : C.Mem model)
    (assignment : S.Assignment)
    (sourceSupported : q.sourceTerm.SupportedAt model assignment) :
    0 <
      ((denominator.supported model member assignment
          (q.jointDenominator.supportedAt model assignment)).endpoints.2).1.num := by
  let bayesSupported :=
    conditionalBayes_supportedAt model q assignment sourceSupported
  have quotientSupported : ProbabilityResult.Supported
      (ProbabilityResult.divide
        (q.jointNumerator.sourceTerm.denote model assignment)
        (q.jointDenominator.sourceTerm.denote model assignment)) := by
    simpa [ProbabilityTerm.denote] using bayesSupported
  rcases ProbabilityResult.positiveDenominatorOfSupportedDivide
      quotientSupported with
    ⟨sourceValue, sourceValueEquivalent, sourceValuePositive⟩
  let sourceTermSupported :=
    q.jointDenominator.supportedAt model assignment
  let derivationSupported :=
    denominator.supported model member assignment sourceTermSupported
  let formulaSupported := derivationSupported.endpoints.2
  have sourceToFormula : ProbabilityTerm.EquivalentAt model
      q.jointDenominator.sourceTerm denominator.formula assignment :=
    (denominator.compile).denotational_soundAt sound model member assignment
      sourceTermSupported
  have formulaToSourceValue : ProbabilityResult.Equivalent
      (denominator.formula.denote model assignment) (some sourceValue) :=
    ProbabilityResult.trans (ProbabilityResult.symm sourceToFormula)
      sourceValueEquivalent
  have displayedEquivalent : QProb.Equiv formulaSupported.1 sourceValue := by
    have between := ProbabilityResult.trans
      (ProbabilityResult.symm formulaSupported.2) formulaToSourceValue
    cases between with
    | value equivalent => exact equivalent
  exact (QProb.equiv_num_pos_iff displayedEquivalent).mpr sourceValuePositive

/--
Compile a conditional certificate from arbitrary certificates for its two
Bayes joints.

Unlike `ofJointCertificatesFrom`, this constructor does not require the
denominator formula to be positive outside the support of the source
conditional.  At each supported assignment it obtains precisely the needed
local fact from `denominatorFormulaPositiveAt`.  This is the form required by
a general IDC completeness compiler: recursive joint certificates may return
any action-free formula, not only a complementary observational marginal or
one of the currently recognized product forms.
-/
noncomputable def publishedConditionalCertificateOfJointCertificates
    {S : ObservedSignature} {G : ObservedGraph S}
    {C : GraphModelClass G} (sound : PublishedSoundness S G)
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (numerator : PublishedJointCertificate C correct q.jointNumerator)
    (denominator : PublishedJointCertificate C correct q.jointDenominator) :
    PublishedConditionalCertificate C correct q where
  formula := .divide numerator.formula denominator.formula
  actionFree := ⟨numerator.actionFree, denominator.actionFree⟩
  derivation :=
    ofJointIdentifiedIdDerivation q numerator.derivation
      denominator.derivation
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      ofJointIdentifiedIdDerivation, conditionalBayesDerivation]
    let sourceBayesSupported :=
      conditionalBayes_supportedAt model q assignment sourceSupported
    let sourceDivideSupported :=
      ProbabilityTerm.SupportedAt.congr
        (ConditionalKernelQuery.bayesDivide_eq_conditioningRight q)
        sourceBayesSupported
    let numeratorSupported :=
      numerator.supported model member assignment
        (q.jointNumerator.supportedAt model assignment)
    let denominatorSupported :=
      denominator.supported model member assignment
        (q.jointDenominator.supportedAt model assignment)
    let formulaSupported := ProbabilityTerm.divide_supportedAt
      numeratorSupported.endpoints.2 denominatorSupported.endpoints.2
      (denominator.denominatorFormulaPositiveAt sound correct q model member
        assignment sourceSupported)
    let conditioningLeftSupported :=
      ProbabilityTerm.SupportedAt.congr
        (ConditionalKernelQuery.sourceTerm_eq_conditioningLeft_empty_w q)
        sourceSupported
    exact
      ⟨sourceSupported,
        ⟨formulaSupported,
          ⟨⟨sourceSupported,
              ⟨sourceBayesSupported,
                ⟨conditioningLeftSupported,
                  ⟨sourceDivideSupported, ()⟩⟩⟩⟩,
            ⟨sourceBayesSupported,
              ⟨formulaSupported,
                ⟨numeratorSupported, denominatorSupported⟩⟩⟩⟩⟩⟩

/--
The premise-free public form of support-sensitive Bayes assembly.  Soundness
is not an additional completeness assumption: every finite observed graph
already carries the constructive theorem `ObservedGraph.publishedSoundness`.
Keeping this wrapper at the assembly boundary also prevents the core
`Completeness` development from importing its sibling module.
-/
noncomputable def PublishedConditionalCertificate.ofJointCertificates
    {S : ObservedSignature} {G : ObservedGraph S}
    {C : GraphModelClass G} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (numerator : PublishedJointCertificate C correct q.jointNumerator)
    (denominator : PublishedJointCertificate C correct q.jointDenominator) :
    PublishedConditionalCertificate C correct q :=
  publishedConditionalCertificateOfJointCertificates G.publishedSoundness
    correct q numerator denominator

end Causality
end Thesis
