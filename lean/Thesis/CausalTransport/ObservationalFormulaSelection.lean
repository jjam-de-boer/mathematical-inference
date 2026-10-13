import Thesis.CausalTransport.GuardedAdmissibleCertificates
import Thesis.CausalTransport.HiddenDAGAlmostSureIntervention

namespace Thesis
namespace Causality

open Probability

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-!
# Observable selection from a finite certified formula catalogue

The ordinary ID/IDC certificate records its engine's literal output.  It
cannot represent a different formula for the same query.  The independent
certificate below instead stores an observational expression, an explicit
observable guard, and a proved native interpretation on that guarded domain.
Existing engine certificates embed without losing their original result
equations; a probability-one action contributes a genuinely distribution-
specific candidate with a guard that is not silently dropped.

Selection evaluates only the supplied observational probability record.
It checks the guard and actual partial expression, then returns the first
available candidate.  Undefined is never changed to zero.  For conditional
targets, soundness still requests actual source support; observational tests
do not manufacture a causal value at a null original conditioner.

Soundness, agreement of available candidates, and completeness *within the
supplied finite catalogue* are proved separately.  An empty selection means
only that this catalogue has no available candidate, not graph failure or
global non-identifiability.  Nothing here claims maximality over all formulas.
-/

namespace ProbabilityTerm

/-- Evaluate syntax directly from an observational record.  Actionful kernel
leaves are rejected, rather than quietly reinterpreted as observational ones.
For certified action-free terms this is literally the native evaluation. -/
def observationalDenote (record : FiniteProbRecord S.Assignment) :
    ProbabilityTerm S → S.Assignment → ProbabilityResult.Result
  | .zero, _ => some QProb.zero
  | .kernel queryKernel, reference =>
      if queryKernel.hasAction then none else
        ProbabilityResult.divide (some (record.probVal (queryKernel.numeratorEvent reference)))
          (some (record.probVal (queryKernel.conditionEvent reference)))
  | .marginalize nodes inner, reference =>
      ProbabilityResult.sum ((marginalAssignments S nodes reference).map
        (fun variant => inner.observationalDenote record variant))
  | .evaluateAt fixed inner, _ => inner.observationalDenote record fixed
  | .add left right, reference => ProbabilityResult.add
      (left.observationalDenote record reference) (right.observationalDenote record reference)
  | .multiply left right, reference => ProbabilityResult.multiply
      (left.observationalDenote record reference) (right.observationalDenote record reference)
  | .weightedMultiply weight factor, reference => ProbabilityResult.weightedMultiply
      (weight.observationalDenote record reference) (factor.observationalDenote record reference)
  | .divide numerator denominator, reference => ProbabilityResult.divide
      (numerator.observationalDenote record reference) (denominator.observationalDenote record reference)

/-- No hidden mechanism or intervention oracle is used by observational
evaluation of an action-free expression, including its guarded zero branches. -/
theorem observationalDenote_eq_native (model : FiniteHiddenDAGSCM S P)
    (term : ProbabilityTerm S) (actionFree : term.ActionFree) (reference : S.Assignment) :
    term.observationalDenote model.observationalDist reference = model.termDenote term reference := by
  induction term generalizing reference with
  | zero => rfl
  | kernel kernel =>
      have noAction := ProbabilityTerm.actionFree_hasAction_false kernel actionFree
      simp only [observationalDenote, FiniteHiddenDAGSCM.termDenote,
        FiniteHiddenDAGSCM.kernelDenote, FiniteHiddenDAGSCM.kernelDistribution,
        noAction, Bool.false_eq_true, if_false]
  | marginalize nodes inner inductionHypothesis =>
      simp only [observationalDenote, FiniteHiddenDAGSCM.termDenote]
      have same : (fun variant => inner.observationalDenote model.observationalDist variant) =
          (fun variant => model.termDenote inner variant) :=
        funext (inductionHypothesis actionFree)
      rw [same]
  | evaluateAt fixed inner inductionHypothesis => exact inductionHypothesis actionFree fixed
  | add left right leftIH rightIH =>
      simp only [observationalDenote, FiniteHiddenDAGSCM.termDenote,
        leftIH actionFree.1 reference, rightIH actionFree.2 reference]
  | multiply left right leftIH rightIH =>
      simp only [observationalDenote, FiniteHiddenDAGSCM.termDenote,
        leftIH actionFree.1 reference, rightIH actionFree.2 reference]
  | weightedMultiply weight factor weightIH factorIH =>
      simp only [observationalDenote, FiniteHiddenDAGSCM.termDenote,
        weightIH actionFree.1 reference, factorIH actionFree.2 reference]
  | divide numerator denominator numeratorIH denominatorIH =>
      simp only [observationalDenote, FiniteHiddenDAGSCM.termDenote,
        numeratorIH actionFree.1 reference, denominatorIH actionFree.2 reference]

end ProbabilityTerm

/-- Explicit observable applicability beyond printed support.  Probability
one is needed only by the distribution-specific candidate; a graph-valid
formula can use `always`.  More guards can be added with their own invariance
proofs, without adding unproved causal rules to the derivation language. -/
inductive ObservationalFormulaGuard (S : ObservedSignature) where
  | always
  | actionOne (action : NodeSet S)

namespace ObservationalFormulaGuard

def check (guard : ObservationalFormulaGuard S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) : Bool :=
  match guard with
  | .always => true
  | .actionOne action =>
      let probability := record.probVal (Kernel.agreesOn action reference)
      decide (probability.num = probability.den)

/-- The executable natural-number equality is exactly rational probability
one; it makes no decision about an arbitrary mathematical proposition. -/
theorem check_actionOne_iff (action : NodeSet S) (record : FiniteProbRecord S.Assignment)
    (reference : S.Assignment) :
    check (.actionOne action) record reference = true ↔
      QProb.Equiv (record.probVal (Kernel.agreesOn action reference)) QProb.one := by
  simp only [check, decide_eq_true_eq, QProb.Equiv, QProb.one, Nat.mul_one, Nat.one_mul]

/-- Guards are properties of the whole observed law, not of a model's
hidden implementation.  Unreduced but equivalent fractions give the same
probability-one acceptance, by transitivity of rational equivalence. -/
theorem check_transfer (guard : ObservationalFormulaGuard S)
    {left right : FiniteHiddenDAGSCM S P} (observational : left.ObservationalAgreement right)
    (reference : S.Assignment) (accepted : guard.check left.observationalDist reference = true) :
    guard.check right.observationalDist reference = true := by
  cases guard with
  | always => rfl
  | actionOne action =>
      exact (check_actionOne_iff action right.observationalDist reference).mpr
        (FiniteHiddenDAGSCM.action_probability_one_transfer observational action reference
          ((check_actionOne_iff action left.observationalDist reference).mp accepted))

end ObservationalFormulaGuard

/-- A formula-independent native certificate.  Source support is explicit
so this common API also handles conditional queries without filling null
conditioners.  The observable guard is an additional assumption, not a claim
that the mere definedness of an arbitrary expression identifies its source. -/
structure GuardedObservationalFormula (projection : FiniteLatentProjection S)
    (source : ProbabilityTerm S) where
  formula : ProbabilityTerm S
  actionFree : formula.ActionFree
  guard : ObservationalFormulaGuard S
  interpret : forall model : FiniteHiddenDAGSCM S projection, forall reference,
    guard.check model.observationalDist reference = true →
    model.TermSupportedAt source reference → model.TermSupportedAt formula reference →
    model.TermEquivalentAt source formula reference

namespace GuardedObservationalFormula

/-- Acceptance is entirely observable: the guard must pass and the actual
printed formula must have a value.  A defined zero is available; `none` is not. -/
def available (candidate : GuardedObservationalFormula P source)
    (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) : Bool :=
  candidate.guard.check record reference &&
    (candidate.formula.observationalDenote record reference).isSome

/-- Construct the printed support value directly from the evaluated option.
No value is extracted from a propositional existential by choice. -/
noncomputable def printedSupported (candidate : GuardedObservationalFormula P source)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (accepted : candidate.available model.observationalDist reference = true) :
    model.TermSupportedAt candidate.formula reference := by
  have defined := (Bool.and_eq_true_iff.mp accepted).2
  rw [ProbabilityTerm.observationalDenote_eq_native model candidate.formula candidate.actionFree reference] at defined
  cases result : model.termDenote candidate.formula reference with
  | none => simp only [result, Option.isSome_none, Bool.false_eq_true] at defined
  | some value =>
      exact ⟨value, by rw [result]; exact .value (QProb.equiv_refl value)⟩

/-- Every accepted candidate computes its genuine supported native source.
The source premise is automatic for an unconditional joint target, but not
silently inferred for an arbitrary conditional target. -/
noncomputable def soundAt (candidate : GuardedObservationalFormula P source)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (sourceSupported : model.TermSupportedAt source reference)
    (accepted : candidate.available model.observationalDist reference = true) :
    model.TermEquivalentAt source candidate.formula reference :=
  candidate.interpret model reference (Bool.and_eq_true_iff.mp accepted).1
    sourceSupported (candidate.printedSupported model reference accepted)

/-- Different accepted candidates agree because both compute the same
supported source.  Formula syntax and unreduced rational representations
may differ; ordinary partial-result equivalence is the comparison. -/
noncomputable def agreeAt (left right : GuardedObservationalFormula P source)
    (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (sourceSupported : model.TermSupportedAt source reference)
    (leftAccepted : left.available model.observationalDist reference = true)
    (rightAccepted : right.available model.observationalDist reference = true) :
    model.TermEquivalentAt left.formula right.formula reference :=
  ProbabilityResult.trans (ProbabilityResult.symm (left.soundAt model reference sourceSupported leftAccepted))
    (right.soundAt model reference sourceSupported rightAccepted)

/-- Read a joint engine certificate as one candidate while retaining its
original separate engine-result certificate unchanged. -/
noncomputable def ofJoint {query : JointKernelQuery S}
    (certificate : PublishedAdmissibleJointCertificate P query) :
    GuardedObservationalFormula P query.sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  guard := .always
  interpret := fun model reference _ _ printed => certificate.intrinsic_soundAt model reference
    ((model.usedConditionalsAdmissibleAt_iff_supported certificate.formula reference).mpr ⟨printed⟩)

/-- The conditional adapter retains actual original source support rather
than treating positive displayed denominators as evidence for that source. -/
noncomputable def ofConditional {query : ConditionalKernelQuery S}
    (certificate : PublishedAdmissibleConditionalCertificate P query) :
    GuardedObservationalFormula P query.sourceTerm where
  formula := certificate.formula
  actionFree := certificate.actionFree
  guard := .always
  interpret := fun model reference _ sourceSupported printed => certificate.intrinsic_soundAt model reference
    ((model.conditioningAdmissibleAt_iff_supported query.operationKernel reference).mpr ⟨sourceSupported⟩)
    ((model.usedConditionalsAdmissibleAt_iff_supported certificate.formula reference).mpr ⟨printed⟩)

/-- A genuinely law-specific candidate.  The observational kernel is always
the same syntax, but its use as a causal formula requires the probability-one
guard.  It is not inserted as an unqualified graph-level identification. -/
noncomputable def ofActionOne (kernel : Kernel S) :
    GuardedObservationalFormula P (.kernel kernel) where
  formula := .kernel ⟨kernel.outcome, NodeSet.empty, kernel.condition⟩
  actionFree := fun _ => rfl
  guard := .actionOne kernel.action
  interpret := fun model reference accepted _ _ => model.kernel_eq_observational_of_action_one kernel reference
    ((ObservationalFormulaGuard.check_actionOne_iff kernel.action model.observationalDist reference).mp accepted)

/-- Deterministic finite search.  Its result contains an actual candidate,
not a formula selected from an existential semantic theorem. -/
def select (record : FiniteProbRecord S.Assignment) (reference : S.Assignment) :
    List (GuardedObservationalFormula P source) → Option (GuardedObservationalFormula P source)
  | [] => none
  | candidate :: candidates =>
      if candidate.available record reference then some candidate else select record reference candidates

theorem select_available (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (candidates : List (GuardedObservationalFormula P source))
    (chosen : GuardedObservationalFormula P source)
    (selected : select record reference candidates = some chosen) : chosen.available record reference = true := by
  induction candidates with
  | nil => cases selected
  | cons candidate candidates inductionHypothesis =>
      cases accepted : candidate.available record reference with
      | false =>
          exact inductionHypothesis (by simpa only [select, accepted, Bool.false_eq_true, if_false] using selected)
      | true =>
          have same : candidate = chosen := Option.some.inj
            (by simpa only [select, accepted, if_true] using selected)
          rw [← same]
          exact accepted

/-- Exact relative failure: every listed candidate is unavailable.  This
does not refute a missing candidate or a distribution-specific reduction. -/
theorem select_none_iff (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (candidates : List (GuardedObservationalFormula P source)) :
    select record reference candidates = none ↔
      forall candidate, candidate ∈ candidates → candidate.available record reference = false := by
  induction candidates with
  | nil =>
      constructor
      · intro _ candidate member; cases member
      · intro _; rfl
  | cons candidate candidates inductionHypothesis =>
      cases accepted : candidate.available record reference with
      | false =>
          constructor
          · intro failed chosen member
            have tail : select record reference candidates = none := by
              simpa only [select, accepted, Bool.false_eq_true, if_false] using failed
            rcases List.mem_cons.mp member with same | listed
            · subst chosen; exact accepted
            · exact inductionHypothesis.mp tail chosen listed
          · intro unavailable
            have tail := inductionHypothesis.mpr (fun chosen listed =>
              unavailable chosen (List.mem_cons_of_mem candidate listed))
            simpa only [select, accepted, Bool.false_eq_true, if_false] using tail
      | true =>
          constructor
          · intro failed
            simp only [select, accepted, if_true, Option.some_ne_none] at failed
          · intro unavailable
            have impossible := unavailable candidate List.mem_cons_self
            rw [accepted] at impossible
            cases impossible

/-- Completeness only within the supplied finite family: any available
member forces search to return an available candidate. -/
theorem select_complete (record : FiniteProbRecord S.Assignment) (reference : S.Assignment)
    (candidates : List (GuardedObservationalFormula P source))
    (available : ∃ candidate, candidate ∈ candidates ∧ candidate.available record reference = true) :
    ∃ chosen, select record reference candidates = some chosen := by
  cases result : select record reference candidates with
  | some chosen => exact ⟨chosen, rfl⟩
  | none =>
      rcases available with ⟨candidate, listed, accepted⟩
      have unavailable := (select_none_iff record reference candidates).mp result candidate listed
      rw [accepted] at unavailable
      cases unavailable

/-- The selected formula's soundness is inherited from its proved candidate
interpretation.  No claim about global maximality is hidden in the search. -/
noncomputable def select_soundAt (model : FiniteHiddenDAGSCM S P) (reference : S.Assignment)
    (candidates : List (GuardedObservationalFormula P source))
    (chosen : GuardedObservationalFormula P source)
    (selected : select model.observationalDist reference candidates = some chosen)
    (sourceSupported : model.TermSupportedAt source reference) :
    model.TermEquivalentAt source chosen.formula reference :=
  chosen.soundAt model reference sourceSupported
    (select_available model.observationalDist reference candidates chosen selected)

end GuardedObservationalFormula
end Causality
end Thesis
