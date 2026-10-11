import Thesis.CausalTransport.HiddenDAGCollapse
import Thesis.CausalTransport.HiddenDAG
import Thesis.Causality.ObservationalSupport

namespace Thesis
namespace Causality

open Probability

universe u

variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Native probability terms and local support in full hidden DAGs

Every kernel below uses the original hidden-DAG model's observational or
hard-interventional finite record.  Compound terms recurse over those native
kernel results, with the same finite substitution enumeration as the intrinsic
language.  Native semantics is not defined by evaluating the collapsed model.

The intervention-preserving collapse separately proves literal equality of
kernel distributions and every partial term result.  Thus a missing result
stays missing, a zero stays zero, and local support evidence transports in
both directions without selecting a conditional value at a null event.

The recursive support tree is native too.  It records supported endpoints and
exactly the subderivations required by each constructor.  Guarded congruence
retains its factor subtree only under a positive native weight.  This module
provides the semantic bridge for soundness; it does not assume a published
latent-projection interface or supply the remaining completeness countermodels.
-/

namespace FiniteHiddenDAGSCM

/-! ## Direct finite-record and expression evaluation -/

/-- Select the original model's actual distribution for this query.  Hard
interventions use the reference values, and the empty-action branch retains
the original observational record. -/
def kernelDistribution (M : FiniteHiddenDAGSCM S P) (kernel : Kernel S)
    (reference : S.Assignment) : FiniteProbRecord S.Assignment :=
  if kernel.hasAction then
    M.interventionalDist { value := kernel.intervention reference }
  else M.observationalDist

/-- Interpret the actual finite numerator and conditioner of a native kernel.
Zero denominators remain undefined; no completion of `0 / 0` is introduced. -/
def kernelDenote (M : FiniteHiddenDAGSCM S P) (kernel : Kernel S)
    (reference : S.Assignment) : ProbabilityResult.Result :=
  let distribution := M.kernelDistribution kernel reference
  let denominator := distribution.probVal (kernel.conditionEvent reference)
  let numerator := distribution.probVal (kernel.numeratorEvent reference)
  ProbabilityResult.divide (some numerator) (some denominator)

/-- Evaluate every probability-term constructor with native kernel semantics.
The distinguished left weight of a guarded product is retained; neither
commutation nor association with the old strict product is assumed. -/
def termDenote (M : FiniteHiddenDAGSCM S P) :
    ProbabilityTerm S -> S.Assignment -> ProbabilityResult.Result
  | .zero, _ => some QProb.zero
  | .kernel kernel, assignment => M.kernelDenote kernel assignment
  | .marginalize nodes inner, assignment =>
      ProbabilityResult.sum
        ((ProbabilityTerm.marginalAssignments S nodes assignment).map
          (fun variant => M.termDenote inner variant))
  | .evaluateAt fixed inner, _ => M.termDenote inner fixed
  | .add left right, assignment =>
      ProbabilityResult.add (M.termDenote left assignment) (M.termDenote right assignment)
  | .multiply left right, assignment =>
      ProbabilityResult.multiply (M.termDenote left assignment) (M.termDenote right assignment)
  | .weightedMultiply weight factor, assignment =>
      ProbabilityResult.weightedMultiply
        (M.termDenote weight assignment) (M.termDenote factor assignment)
  | .divide numerator denominator, assignment =>
      ProbabilityResult.divide
        (M.termDenote numerator assignment) (M.termDenote denominator assignment)

/-- Constructive native support at one valuation, with the rational value
retained as data rather than selected from a truncated existence proof. -/
def TermSupportedAt (M : FiniteHiddenDAGSCM S P)
    (term : ProbabilityTerm S) (assignment : S.Assignment) : Type :=
  ProbabilityResult.Supported (M.termDenote term assignment)

/-- Native partial-result equivalence at one valuation.  This distinguishes
unsupported conditionals from supported zeros. -/
def TermEquivalentAt (M : FiniteHiddenDAGSCM S P)
    (left right : ProbabilityTerm S) (assignment : S.Assignment) : Type :=
  ProbabilityResult.Equivalent (M.termDenote left assignment) (M.termDenote right assignment)

/-! ## Literal preservation, including undefined results -/

theorem kernelDistribution_preserved (M : FiniteHiddenDAGSCM S P)
    (kernel : Kernel S) (assignment : S.Assignment) :
    M.kernelDistribution kernel assignment =
      kernel.distribution M.toLatentRootSCM assignment := by
  unfold kernelDistribution Kernel.distribution
  split
  · exact (M.toLatentRootSCM_interventionalDist
      { value := kernel.intervention assignment }).symm
  · exact M.toLatentRootSCM_observationalDist.symm

/-- Kernel preservation is literal result equality, not merely a positive-
support or selected-event comparison.  Undefined conditioners are included. -/
theorem kernelDenote_preserved (M : FiniteHiddenDAGSCM S P)
    (kernel : Kernel S) (assignment : S.Assignment) :
    M.kernelDenote kernel assignment = kernel.denote M.toLatentRootSCM assignment := by
  unfold kernelDenote Kernel.denote
  rw [M.kernelDistribution_preserved kernel assignment]

/-- All compound partial results are preserved.  Finite marginalization uses
the same native substitutions; the induction replaces their evaluated terms
without any support premise or probability-algebra cancellation. -/
theorem termDenote_preserved (M : FiniteHiddenDAGSCM S P)
    (term : ProbabilityTerm S) : forall assignment,
    M.termDenote term assignment = term.denote M.toLatentRootSCM assignment := by
  intro assignment
  induction term generalizing assignment with
  | zero => rfl
  | kernel kernel => exact M.kernelDenote_preserved kernel assignment
  | marginalize nodes inner inductionHypothesis =>
      simp only [termDenote, ProbabilityTerm.denote]
      have valuesEqual :
          (fun variant => M.termDenote inner variant) =
          (fun variant => inner.denote M.toLatentRootSCM variant) :=
        funext inductionHypothesis
      rw [valuesEqual]
  | evaluateAt fixed inner inductionHypothesis => exact inductionHypothesis fixed
  | add left right leftIH rightIH =>
      simp only [termDenote, ProbabilityTerm.denote, leftIH assignment, rightIH assignment]
  | multiply left right leftIH rightIH =>
      simp only [termDenote, ProbabilityTerm.denote, leftIH assignment, rightIH assignment]
  | weightedMultiply weight factor weightIH factorIH =>
      simp only [termDenote, ProbabilityTerm.denote, weightIH assignment, factorIH assignment]
  | divide numerator denominator numeratorIH denominatorIH =>
      simp only [termDenote, ProbabilityTerm.denote,
        numeratorIH assignment, denominatorIH assignment]

/-- Keep the same support value when moving a native result to the collapsed
semantics.  Equality of results, rather than a new witness choice, does the work. -/
noncomputable def termSupportedAt_to_collapsed (M : FiniteHiddenDAGSCM S P)
    (term : ProbabilityTerm S) (assignment : S.Assignment)
    (supported : M.TermSupportedAt term assignment) :
    term.SupportedAt M.toLatentRootSCM assignment := by
  change ProbabilityResult.Supported (M.termDenote term assignment) at supported
  rw [M.termDenote_preserved term assignment] at supported
  exact supported

/-- Read collapsed support back in the original full-model semantics. -/
noncomputable def termSupportedAt_of_collapsed (M : FiniteHiddenDAGSCM S P)
    (term : ProbabilityTerm S) (assignment : S.Assignment)
    (supported : term.SupportedAt M.toLatentRootSCM assignment) :
    M.TermSupportedAt term assignment := by
  change ProbabilityResult.Supported (M.termDenote term assignment)
  rw [M.termDenote_preserved term assignment]
  exact supported

/-- Transfer an equivalence without changing its support domain. -/
noncomputable def termEquivalentAt_of_collapsed (M : FiniteHiddenDAGSCM S P)
    (left right : ProbabilityTerm S) (assignment : S.Assignment)
    (equivalent : ProbabilityTerm.EquivalentAt M.toLatentRootSCM left right assignment) :
    M.TermEquivalentAt left right assignment := by
  change ProbabilityResult.Equivalent (M.termDenote left assignment) (M.termDenote right assignment)
  rw [M.termDenote_preserved left assignment, M.termDenote_preserved right assignment]
  exact equivalent

/-! ## Observable local overlap, not global positivity -/

/-- Positive mass of one factual cylinder in the original hidden-DAG model. -/
def ObservationalCylinderPositiveAt (M : FiniteHiddenDAGSCM S P)
    (nodes : NodeSet S) (reference : S.Assignment) : Prop :=
  0 < (M.observationalDist.probVal (Kernel.agreesOn nodes reference)).num

/-- Every unconditional native kernel is supported, including zero outcomes.
Its support value is the actual cylinder probability of the original record. -/
noncomputable def kernelSupportedAt_unconditional (M : FiniteHiddenDAGSCM S P)
    (outcome action : NodeSet S) (assignment : S.Assignment) :
    M.TermSupportedAt (.kernel ⟨outcome, action, NodeSet.empty⟩) assignment := by
  let kernel : Kernel S := ⟨outcome, action, NodeSet.empty⟩
  refine ⟨(M.kernelDistribution kernel assignment).probVal
    (Kernel.agreesOn outcome assignment), ?_⟩
  change ProbabilityResult.Equivalent (M.kernelDenote kernel assignment)
    (some ((M.kernelDistribution kernel assignment).probVal (Kernel.agreesOn outcome assignment)))
  rw [M.kernelDenote_preserved, M.kernelDistribution_preserved]
  exact Kernel.unconditionalDenote M.toLatentRootSCM outcome action assignment

/-- Observable action-and-condition overlap supplies actual native kernel
support.  Outcomes may have zero mass, and no canonical-root or graph premise
is needed for this consistency-based probability fact. -/
noncomputable def kernelSupportedAt_of_observational_overlap
    (M : FiniteHiddenDAGSCM S P) (kernel : Kernel S) (assignment : S.Assignment)
    (overlap : M.ObservationalCylinderPositiveAt
      (NodeSet.union kernel.action kernel.condition) assignment) :
    M.TermSupportedAt (.kernel kernel) assignment := by
  have collapsedOverlap : Causality.ObservationalCylinderPositiveAt
      M.toLatentRootSCM (NodeSet.union kernel.action kernel.condition) assignment := by
    change 0 < (M.toLatentRootSCM.observationalDist.probVal
      (Kernel.agreesOn (NodeSet.union kernel.action kernel.condition) assignment)).num
    rw [M.toLatentRootSCM_observationalDist]
    exact overlap
  exact M.termSupportedAt_of_collapsed (.kernel kernel) assignment
    (Kernel.supportedAt_of_observational_overlap M.toLatentRootSCM kernel assignment collapsedOverlap)

/-- Agreement of the native observational records, without a model-class
restriction or a global support requirement. -/
def ObservationalAgreement (left right : FiniteHiddenDAGSCM S P) : Prop :=
  forall event, QProb.Equiv (left.observationalValue event) (right.observationalValue event)

/-- The observable overlap condition automatically transfers between models
with the same observational law.  Only the first model needs to supply it. -/
theorem ObservationalCylinderPositiveAt.transfer
    {left right : FiniteHiddenDAGSCM S P} (observational : left.ObservationalAgreement right)
    {nodes : NodeSet S} {assignment : S.Assignment}
    (overlap : left.ObservationalCylinderPositiveAt nodes assignment) :
    right.ObservationalCylinderPositiveAt nodes assignment :=
  (QProb.equiv_num_pos_iff (observational (Kernel.agreesOn nodes assignment))).mp overlap

/-- Action-free formulas depend only on the original observational record.
The collapse identities justify the transport; no hidden-DAG identification
or latent-projection theorem is assumed as an extra field. -/
noncomputable def actionFree_invariant (left right : FiniteHiddenDAGSCM S P)
    (observational : left.ObservationalAgreement right) (term : ProbabilityTerm S)
    (actionFree : term.ActionFree) (assignment : S.Assignment) :
    ProbabilityResult.Equivalent (left.termDenote term assignment) (right.termDenote term assignment) := by
  rw [left.termDenote_preserved term assignment, right.termDenote_preserved term assignment]
  apply ProbabilityTerm.actionFree_invariant _ _ _ term actionFree assignment
  intro event
  rw [left.toLatentRootSCM_observationalValue event, right.toLatentRootSCM_observationalValue event]
  exact observational event

end FiniteHiddenDAGSCM

/-- Native recursive support for an arbitrary do-calculus derivation.  The
graph only indexes syntax; soundness will separately use the actual projection.
Guarded factor support is requested only under a positive *native* weight. -/
def HiddenDAGLocalDerivationSupport {G : ObservedGraph S}
    (model : FiniteHiddenDAGSCM S P) (assignment : S.Assignment)
    {left right : ProbabilityTerm S} (derivation : DoCalculusDerivation G left right) : Type :=
  model.TermSupportedAt left assignment × model.TermSupportedAt right assignment ×
    match derivation with
    | .refl _ => Unit
    | .symm inner => HiddenDAGLocalDerivationSupport model assignment inner
    | .trans first second =>
        HiddenDAGLocalDerivationSupport model assignment first ×
          HiddenDAGLocalDerivationSupport model assignment second
    | .doRule _ => Unit
    | .marginalization _ _ _ _ _ => Unit
    | .conditioning _ _ _ _ _ => Unit
    | .chain _ _ _ _ _ => Unit
    | .weightedChain _ _ _ _ _ => Unit
    | .multiplyComm _ _ => Unit
    | .multiplyAssoc _ _ _ => Unit
    | .marginalizeCongr nodes inner =>
        forall variant, variant ∈ ProbabilityTerm.marginalAssignments S nodes assignment ->
          HiddenDAGLocalDerivationSupport model variant inner
    | .evaluateAtCongr fixed inner => HiddenDAGLocalDerivationSupport model fixed inner
    | .addCongr first second =>
        HiddenDAGLocalDerivationSupport model assignment first ×
          HiddenDAGLocalDerivationSupport model assignment second
    | .multiplyCongr first second =>
        HiddenDAGLocalDerivationSupport model assignment first ×
          HiddenDAGLocalDerivationSupport model assignment second
    | @DoCalculusDerivation.weightedMultiplyCongr _ _ _ weight _ _ _ first second =>
        HiddenDAGLocalDerivationSupport model assignment first ×
          (ProbabilityResult.PositiveSupportedValue (model.termDenote weight assignment) ->
            HiddenDAGLocalDerivationSupport model assignment second)
    | .divideCongr numerator denominator =>
        HiddenDAGLocalDerivationSupport model assignment numerator ×
          HiddenDAGLocalDerivationSupport model assignment denominator
    | .eqCongr _ _ inner => HiddenDAGLocalDerivationSupport model assignment inner

/-- Interpret the complete native support tree in the collapsed model.
Each required marginal substitution is retained.  In a guarded branch the
positive-weight evidence is moved back through literal term preservation
before calling the supplied native factor-support function. -/
noncomputable def HiddenDAGLocalDerivationSupport.toCollapsed
    {G : ObservedGraph S} {model : FiniteHiddenDAGSCM S P} {assignment : S.Assignment}
    {left right : ProbabilityTerm S} {derivation : DoCalculusDerivation G left right}
    (supported : HiddenDAGLocalDerivationSupport model assignment derivation) :
    LocalDerivationSupport model.toLatentRootSCM assignment derivation := by
  induction derivation generalizing assignment with
  | refl =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ()⟩
  | symm inner ih =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ih supported.2.2⟩
  | trans first second firstIH secondIH =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1,
        firstIH supported.2.2.1, secondIH supported.2.2.2⟩
  | doRule =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ()⟩
  | marginalization =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ()⟩
  | conditioning =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ()⟩
  | chain =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ()⟩
  | weightedChain =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ()⟩
  | multiplyComm =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ()⟩
  | multiplyAssoc =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ()⟩
  | marginalizeCongr nodes inner ih =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1,
        fun variant member => ih (supported.2.2 variant member)⟩
  | evaluateAtCongr fixed inner ih =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ih supported.2.2⟩
  | addCongr first second firstIH secondIH =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1,
        firstIH supported.2.2.1, secondIH supported.2.2.2⟩
  | multiplyCongr first second firstIH secondIH =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1,
        firstIH supported.2.2.1, secondIH supported.2.2.2⟩
  | @weightedMultiplyCongr weight _ _ _ first second firstIH secondIH =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1,
        firstIH supported.2.2.1, fun positive => secondIH (supported.2.2.2 (by
          rw [model.termDenote_preserved weight assignment]
          exact positive))⟩
  | divideCongr numerator denominator numeratorIH denominatorIH =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1,
        numeratorIH supported.2.2.1, denominatorIH supported.2.2.2⟩
  | eqCongr _hleft _hright inner ih =>
      exact ⟨model.termSupportedAt_to_collapsed _ _ supported.1,
        model.termSupportedAt_to_collapsed _ _ supported.2.1, ih supported.2.2⟩

namespace HiddenDAGModelFamily

/-- The native kernel semantics agrees definitionally with the existing
family-level query API, for every selected family as well as the full family.
This does not assert identifiability equivalence between different families. -/
theorem kernelResult_eq_native (family : HiddenDAGModelFamily S P)
    (model : family.Model) (kernel : Kernel S) (assignment : S.Assignment) :
    family.kernelResult model kernel assignment =
      (family.semantics model).kernelDenote kernel assignment := rfl

end HiddenDAGModelFamily
end Causality
end Thesis
