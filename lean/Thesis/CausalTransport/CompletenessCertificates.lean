import Thesis.CausalTransport.Correspondence
import Thesis.CausalTransport.ActionDeletion
import Thesis.CausalTransport.ConditionalBayes
import Thesis.Causality.TermSupport
import Thesis.Causality.CForestConstruction
import Thesis.CausalTransport.DSeparationCorrectness
import Thesis.Causality.Legacy.IdentificationInduction
import Thesis.Causality.IdentificationSearch
import Thesis.Causality.IdentificationRank
import Thesis.Causality.PairRoot
import Thesis.Probability.ConstructivePermutation

namespace Thesis
namespace Causality

open Probability

/-!
# Certificates, structural traces and finite branch leaves

Retains the original joint/conditional certificate constructors, support
arguments, legacy trace totality and reusable finite graph leaves.

Every extracted declaration keeps its original namespace, statement, proof
script and order. The new boundary only lets later work import a completed
artifact instead of retaining this section's elaboration state. Existing
clients may still import Completeness for the entire historical interface.
No theorem is dropped, weakened or replaced by an assumption.

Historical branch-specific unpackers remain historical facts: their quantity
is not evidence that a published semantic completeness theorem has been
inhabited. Current-engine compilation and hedge semantics retain their
existing independently checked assembly boundaries.
-/

/-! ## Successful identification certificates and reusable branch leaves -/

/-!
### Top-level structural traces

The generic trace relations retain every argument of `Legacy.identifyFuel`.  These
aliases specialize them to the public `Legacy.identifyJoint` invocation, so subsequent
completeness proofs can enter structural induction without repeatedly exposing
the engine's fuel, full remaining set, and observational starting term.
-/

/-- Structural explanation of a failed top-level joint identification run. -/
abbrev JointIdentificationFailureTrace (G : ObservedGraph S)
    (q : JointKernelQuery S) (fail : IdentificationFail S) : Type :=
  IdentificationFailureTrace G (identificationFuel S) NodeSet.full
    q.outcome q.action (observationalJointTerm S) fail

/-- Structural explanation of a successful top-level joint identification run. -/
abbrev JointIdentificationSuccessTrace (G : ObservedGraph S)
    (q : JointKernelQuery S) (term : ProbabilityTerm S) : Type :=
  IdentificationSuccessTrace G (identificationFuel S) NodeSet.full
    q.outcome q.action (observationalJointTerm S) term

/-- Structural explanation of an unfinished top-level joint identification run. -/
abbrev JointIdentificationUnfinishedTrace (G : ObservedGraph S)
    (q : JointKernelQuery S) : Type :=
  IdentificationUnfinishedTrace G (identificationFuel S) NodeSet.full
    q.outcome q.action (observationalJointTerm S)

/-- Failed public ID runs are exactly top-level structural failure traces. -/
theorem identifyJoint_eq_failed_iff_failureTrace
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) :
    Legacy.identifyJoint G q = IdentificationOutcome.failed fail ↔
      Nonempty (JointIdentificationFailureTrace G q fail) := by
  simpa [Legacy.identifyJoint, JointIdentificationFailureTrace] using
    identifyFuel_eq_failed_iff_failureTrace (identificationFuel S) G
      NodeSet.full q.outcome q.action (observationalJointTerm S) fail

/-- Successful public ID runs are exactly top-level structural success traces. -/
theorem identifyJoint_eq_identified_iff_successTrace
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (term : ProbabilityTerm S) :
    Legacy.identifyJoint G q = IdentificationOutcome.identified term ↔
      Nonempty (JointIdentificationSuccessTrace G q term) := by
  simpa [Legacy.identifyJoint, JointIdentificationSuccessTrace] using
    identifyFuel_eq_identified_iff_successTrace (identificationFuel S) G
      NodeSet.full q.outcome q.action (observationalJointTerm S) term

/-- A top-level structural success trace always ends in an action-free term. -/
theorem JointIdentificationSuccessTrace.actionFree
    {G : ObservedGraph S} {q : JointKernelQuery S}
    {term : ProbabilityTerm S}
    (trace : JointIdentificationSuccessTrace G q term) : term.ActionFree :=
  IdentificationSuccessTrace.actionFree trace
    (observationalJointTerm_actionFree S)

/-- The public unfinished sentinel is exactly a top-level unfinished trace. -/
theorem identifyJoint_eq_unfinished_iff_unfinishedTrace
    (G : ObservedGraph S) (q : JointKernelQuery S) :
    Legacy.identifyJoint G q = IdentificationOutcome.unfinished ↔
      Nonempty (JointIdentificationUnfinishedTrace G q) := by
  simpa [Legacy.identifyJoint, JointIdentificationUnfinishedTrace] using
    identifyFuel_eq_unfinished_iff_unfinishedTrace (identificationFuel S) G
      NodeSet.full q.outcome q.action (observationalJointTerm S)

/--
Constructive top-level case analysis for executable joint identification.

Unlike a disjunction of bare result equations, each case retains the complete
structural trace needed by a downstream induction.  The classifier is obtained
by evaluating `Legacy.identifyJoint` and therefore uses neither excluded middle nor a
choice of a recursive branch.
-/
inductive JointIdentificationTrace (G : ObservedGraph S)
    (q : JointKernelQuery S)
  | identified (term : ProbabilityTerm S)
      (trace : JointIdentificationSuccessTrace G q term)
  | failed (fail : IdentificationFail S)
      (trace : JointIdentificationFailureTrace G q fail)
  | unfinished (trace : JointIdentificationUnfinishedTrace G q)

/-- Every executable joint query has one of the three exact structural traces. -/
noncomputable def identifyJoint_trace (G : ObservedGraph S)
    (q : JointKernelQuery S) :
    JointIdentificationTrace G q := by
  cases result : Legacy.identifyJoint G q with
  | identified term =>
      exact .identified term
        (IdentificationSuccessTrace.of_eq_identified (identificationFuel S) G
          NodeSet.full q.outcome q.action (observationalJointTerm S) term result)
  | failed fail =>
      exact .failed fail
        (IdentificationFailureTrace.of_eq_failed (identificationFuel S) G
          NodeSet.full q.outcome q.action (observationalJointTerm S) result)
  | unfinished =>
      exact .unfinished
        (IdentificationUnfinishedTrace.of_eq_unfinished (identificationFuel S) G
          NodeSet.full q.outcome q.action (observationalJointTerm S) result)

/--
Collapse an arbitrary failed public ID run to the immediate 4.1 invocation at
the end of its structural trace.  This is the branch-generic replacement for
the finite family of `shrink`/`product`/`restrict` failure-stack unpackers.

The returned site is Type-valued inspectable data: later hedge code may recurse
over its local query and component without eliminating an existential
proposition or invoking choice.
-/
noncomputable def identifyJointImmediateFailureSite
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S)
    (result : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    IdentificationImmediateFailureSite G fail :=
  (IdentificationFailureTrace.of_eq_failed (identificationFuel S) G
    NodeSet.full q.outcome q.action (observationalJointTerm S) result).immediateSite

/--
Observational cylinders used as ID denominators are strictly positive in
every member of the classical class.
-/
theorem positive_class_cylinder_positive {G : ObservedGraph S}
    (model : ExactModel S)
    (member : (GraphModelClass.positive G).Mem model)
    (nodes : NodeSet S) (reference : S.Assignment) :
    0 <
      (model.observationalDist.probVal
        (Kernel.agreesOn nodes reference)).num :=
  ObservationallyPositive.cylinder_positive member.2 nodes reference

/--
Empty-action joint queries are solved by ID in one step.  Combined with
soundness of that base case (the observational marginal equals the empty-do
kernel), they are identifiable in every class.
-/
theorem identifyJoint_empty_action_succeeds (G : ObservedGraph S)
    (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    Legacy.identifyJoint G q =
      IdentificationOutcome.identified
        (.marginalize (NodeSet.diff NodeSet.full q.outcome)
          (observationalJointTerm S)) :=
  identifyJoint_of_empty_action G q emptyAction

/-- Successful ID returns an observational (action-free) formula. -/
theorem identifyJoint_success_actionFree
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {term : ProbabilityTerm S}
    (h : Legacy.identifyJoint G q = IdentificationOutcome.identified term) :
    term.ActionFree :=
  identifyJoint_identified_actionFree G q h

/-- An empty-action kernel is already an action-free observational formula. -/
theorem JointKernelQuery.empty_action_free (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    q.sourceTerm.ActionFree := by
  intro i
  exact (NodeSet.isEmpty_eq_true_iff q.action).mp emptyAction i

/--
Empty-action queries are identifiable in every model class: observational
equivalence of action-free kernels is `actionFree_invariant`.
-/
def empty_action_identifiable {G : ObservedGraph S}
    (C : GraphModelClass G) (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    C.identifiable q := by
  intro left right _leftMem _rightMem observational assignment
  exact ⟨ProbabilityTerm.actionFree_invariant left right observational
    q.sourceTerm (q.empty_action_free emptyAction) assignment⟩

/--
The published certificate for an empty-action query is the reflexive
derivation of the source kernel.  No do-rule side condition is required.
-/
def emptyActionPublishedCertificate {G : ObservedGraph S}
    {C : GraphModelClass G} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    PublishedJointCertificate C correct q where
  formula := q.sourceTerm
  actionFree := q.empty_action_free emptyAction
  derivation :=
    @DoCalculusDerivation.refl S G (pathRuleSeparation G) q.sourceTerm
  supported := fun _model _member _assignment sourceSupported =>
    ⟨sourceSupported, ⟨sourceSupported, ()⟩⟩

/-- An empty-action source kernel is the unconditional kernel on the
query outcome.  The equality is `funext` of the Boolean emptiness test,
so it is proof data for `eqCongr` rather than a definitional match. -/
theorem JointKernelQuery.sourceTerm_eq_of_empty_action
    (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    q.sourceTerm =
      .kernel ⟨q.outcome, NodeSet.empty, NodeSet.empty⟩ := by
  have hact : q.action = NodeSet.empty :=
    NodeSet.eq_empty_of_isEmpty emptyAction
  simp [JointKernelQuery.sourceTerm, hact]

/-- Marginalization writes the observational joint as
`P(Y ∪ (V \ Y))`; ID writes it as `P(V)`.  The covering
`NodeSet.union_diff_full` identifies the two kernels. -/
theorem emptyActionMarginalizationTerm_eq_of (outcome : NodeSet S) :
    ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full outcome)
      (.kernel ⟨NodeSet.union outcome
        (NodeSet.diff NodeSet.full outcome),
        NodeSet.empty, NodeSet.empty⟩) =
      ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full outcome)
        (observationalJointTerm S) := by
  simp [observationalJointTerm, NodeSet.union_diff_full]

theorem emptyActionMarginalizationTerm_eq (q : JointKernelQuery S) :
    ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full q.outcome)
      (.kernel ⟨NodeSet.union q.outcome
        (NodeSet.diff NodeSet.full q.outcome),
        NodeSet.empty, NodeSet.empty⟩) =
      ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full q.outcome)
        (observationalJointTerm S) :=
  emptyActionMarginalizationTerm_eq_of q.outcome

/-- The empty-condition observational joint is always defined: its
denominator is the sure event, whose mass is one. -/
noncomputable def observationalJointTerm_supportedAt
    (model : FiniteLatentSCM S) (assignment : S.Assignment) :
    (observationalJointTerm S).SupportedAt model assignment :=
  ⟨((Kernel.mk NodeSet.full NodeSet.empty NodeSet.empty).distribution
      model assignment).probVal (Kernel.agreesOn NodeSet.full assignment),
    by
      simpa [observationalJointTerm, ProbabilityTerm.denote] using
        Kernel.unconditionalDenote model NodeSet.full NodeSet.empty
          assignment⟩

/-- A finite sum of defined observational joints is defined.  This is
the right endpoint of empty-action ID: `∑_{V \ Y} P(V)`. -/
noncomputable def emptyActionMarginal_supportedAt
    (model : FiniteLatentSCM S) (outcome : NodeSet S)
    (assignment : S.Assignment) :
    (ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full outcome)
      (observationalJointTerm S)).SupportedAt model assignment := by
  simpa [ProbabilityTerm.denote] using
    ProbabilityResult.sum_map_supported
      (ProbabilityTerm.marginalAssignments S
        (NodeSet.diff NodeSet.full outcome) assignment)
      (fun variant => (observationalJointTerm S).denote model variant)
      (fun variant => observationalJointTerm_supportedAt model variant)

noncomputable def emptyActionIdentifiedTerm_supportedAt
    (model : FiniteLatentSCM S) (q : JointKernelQuery S)
    (assignment : S.Assignment) :
    (ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full q.outcome)
      (observationalJointTerm S)).SupportedAt model assignment :=
  emptyActionMarginal_supportedAt model q.outcome assignment

/-- Empty-action ID is one application of the marginalization rule, from
`P(Y)` to `∑_{V \ Y} P(Y ∪ (V \ Y))`, reindexed onto the query kernel
and onto `P(V)` by the two `NodeSet` coverings. -/
def emptyActionIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    PathDoCalculusDerivation G q.sourceTerm
      (.marginalize (NodeSet.diff NodeSet.full q.outcome)
        (observationalJointTerm S)) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (JointKernelQuery.sourceTerm_eq_of_empty_action q emptyAction)
    (emptyActionMarginalizationTerm_eq q).symm
    (DoCalculusDerivation.marginalization
      (G := G) (separation := pathRuleSeparation G)
      NodeSet.empty q.outcome (NodeSet.diff NodeSet.full q.outcome)
      NodeSet.empty (FourWayDisjoint.emptyActionMarginal q.outcome))

/-- Empty-action marginalization of an unconditional kernel `P(Y)` onto
the ID formula `∑_{V \ Y} P(V)`. -/
def unconditionalEmptyActionIdDerivation {G : ObservedGraph S}
    (outcome : NodeSet S) :
    PathDoCalculusDerivation G
      (.kernel ⟨outcome, NodeSet.empty, NodeSet.empty⟩)
      (.marginalize (NodeSet.diff NodeSet.full outcome)
        (observationalJointTerm S)) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    rfl
    (emptyActionMarginalizationTerm_eq_of outcome).symm
    (DoCalculusDerivation.marginalization
      (G := G) (separation := pathRuleSeparation G)
      NodeSet.empty outcome (NodeSet.diff NodeSet.full outcome)
      NodeSet.empty (FourWayDisjoint.emptyActionMarginal outcome))

theorem ConditionalKernelQuery.sourceTerm_eq_of_empty_action
    (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    q.sourceTerm =
      .kernel ⟨q.outcome, NodeSet.empty, q.condition⟩ := by
  have hact : q.action = NodeSet.empty :=
    NodeSet.eq_empty_of_isEmpty emptyAction
  simp [ConditionalKernelQuery.sourceTerm, hact]

/-- Empty-action IDC is one application of the conditioning rule: `P(Y | Z)`
rewrites as `P(Y, Z) / P(Z)`, with empty action. -/
def emptyActionConditionalIdDerivation {G : ObservedGraph S}
    (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    PathDoCalculusDerivation G q.sourceTerm
      (.divide
        (.kernel ⟨NodeSet.union q.outcome q.condition,
          NodeSet.empty, NodeSet.empty⟩)
        (.kernel ⟨q.condition, NodeSet.empty, NodeSet.empty⟩)) :=
  have hcond :
      ProbabilityTerm.kernel
        ⟨q.outcome, NodeSet.empty, q.condition⟩ =
      ProbabilityTerm.kernel
        ⟨q.outcome, NodeSet.empty,
          NodeSet.union q.condition NodeSet.empty⟩ := by
    simp [NodeSet.union_empty_right]
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (ConditionalKernelQuery.sourceTerm_eq_of_empty_action q emptyAction)
    rfl
    (DoCalculusDerivation.eqCongr
      (G := G) (separation := pathRuleSeparation G)
      hcond rfl
      (DoCalculusDerivation.conditioning
        (G := G) (separation := pathRuleSeparation G)
        NodeSet.empty q.outcome q.condition NodeSet.empty
        (FourWayDisjoint.emptyActionConditioning q.outcome q.condition
          q.outcome_condition_disjoint)))

/-- Empty-action IDC followed by empty-action ID on both Bayes joints:
`P(Y | Z)` rewrites as the ID formula
`(∑_{V \ (Y ∪ Z)} P(V)) / (∑_{V \ Z} P(V))`. -/
def emptyActionIdentifiedConditionalIdDerivation {G : ObservedGraph S}
    (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    PathDoCalculusDerivation G q.sourceTerm
      (.divide
        (.marginalize
          (NodeSet.diff NodeSet.full
            (NodeSet.union q.outcome q.condition))
          (observationalJointTerm S))
        (.marginalize
          (NodeSet.diff NodeSet.full q.condition)
          (observationalJointTerm S))) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (emptyActionConditionalIdDerivation q emptyAction)
    (DoCalculusDerivation.divideCongr
      (G := G) (separation := pathRuleSeparation G)
      (unconditionalEmptyActionIdDerivation
        (NodeSet.union q.outcome q.condition))
      (unconditionalEmptyActionIdDerivation q.condition))

/-- An empty-action conditional kernel is already action-free. -/
theorem ConditionalKernelQuery.empty_action_free
    (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    q.sourceTerm.ActionFree := by
  intro i
  exact (NodeSet.isEmpty_eq_true_iff q.action).mp emptyAction i

/-- Support of the Bayes formula `P(Y, Z) / P(Z)` at an empty-action
conditional: both joints are unconditional observational kernels, and
the source being defined means `P(Z) > 0`. -/
noncomputable def emptyActionConditionalBayes_supportedAt
    (model : FiniteLatentSCM S) (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true)
    (assignment : S.Assignment)
    (sourceSupported : q.sourceTerm.SupportedAt model assignment) :
    (ProbabilityTerm.divide
      (.kernel ⟨NodeSet.union q.outcome q.condition,
        NodeSet.empty, NodeSet.empty⟩)
      (.kernel ⟨q.condition, NodeSet.empty, NodeSet.empty⟩)).SupportedAt
      model assignment := by
  have hsrc :=
    ConditionalKernelQuery.sourceTerm_eq_of_empty_action q emptyAction
  let srcKernel : Kernel S :=
    ⟨q.outcome, NodeSet.empty, q.condition⟩
  let numKernel : Kernel S :=
    ⟨NodeSet.union q.outcome q.condition, NodeSet.empty, NodeSet.empty⟩
  let denKernel : Kernel S :=
    ⟨q.condition, NodeSet.empty, NodeSet.empty⟩
  have srcSupported' :
      ProbabilityTerm.SupportedAt model (.kernel srcKernel) assignment :=
    ProbabilityTerm.SupportedAt.congr hsrc sourceSupported
  have hdist :
      srcKernel.distribution model assignment =
        denKernel.distribution model assignment :=
    Kernel.distribution_eq_of_action model q.outcome q.condition
      NodeSet.empty q.condition NodeSet.empty assignment
  have hnum :=
    Kernel.unconditionalDenote model
      (NodeSet.union q.outcome q.condition) NodeSet.empty assignment
  have hden :=
    Kernel.unconditionalDenote model q.condition NodeSet.empty assignment
  let numVal :=
    (numKernel.distribution model assignment).probVal
      (Kernel.agreesOn (NodeSet.union q.outcome q.condition) assignment)
  let denVal :=
    (denKernel.distribution model assignment).probVal
      (Kernel.agreesOn q.condition assignment)
  have hpos : 0 < denVal.num := by
    have hsrcPos :=
      Kernel.conditionPositive_of_supportedAt model srcKernel
        assignment srcSupported'
    dsimp [denVal]
    rw [← hdist]
    exact hsrcPos
  have hdiv :
      ProbabilityResult.Equivalent
        ((ProbabilityTerm.divide
          (.kernel numKernel) (.kernel denKernel)).denote model assignment)
        (ProbabilityResult.divide (some numVal) (some denVal)) := by
    simpa [ProbabilityTerm.denote] using
      ProbabilityResult.divide_congr hnum hden
  have hdefinedEq :
      ProbabilityResult.divide (some numVal) (some denVal) =
        some (QProb.div numVal denVal hpos) := by
    simp only [ProbabilityResult.divide]
    rw [dif_pos hpos]
  have hdefined :
      ProbabilityResult.Equivalent
        (ProbabilityResult.divide (some numVal) (some denVal))
        (some (QProb.div numVal denVal hpos)) := by
    rw [hdefinedEq]
    exact ProbabilityResult.Equivalent.value (QProb.equiv_refl _)
  exact ⟨QProb.div numVal denVal hpos,
    ProbabilityResult.trans hdiv hdefined⟩

/-- Local support tree of empty-action Bayes: two `eqCongr` wrappers
around the conditioning leaf. -/
noncomputable def emptyActionConditionalIdDerivation_supported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true)
    (model : FiniteLatentSCM S) (assignment : S.Assignment)
    (sourceSupported : q.sourceTerm.SupportedAt model assignment)
    (formulaSupported :
      (ProbabilityTerm.divide
        (.kernel ⟨NodeSet.union q.outcome q.condition,
          NodeSet.empty, NodeSet.empty⟩)
        (.kernel ⟨q.condition, NodeSet.empty, NodeSet.empty⟩)).SupportedAt
        model assignment) :
    LocalDerivationSupport model assignment
      ((emptyActionConditionalIdDerivation (G := G) q emptyAction).compile
        correct) :=
  let hleft :=
    ConditionalKernelQuery.sourceTerm_eq_of_empty_action q emptyAction
  let hcond :
      ProbabilityTerm.kernel
        ⟨q.outcome, NodeSet.empty, q.condition⟩ =
      ProbabilityTerm.kernel
        ⟨q.outcome, NodeSet.empty,
          NodeSet.union q.condition NodeSet.empty⟩ := by
    simp [NodeSet.union_empty_right]
  let innerLeft :=
    ProbabilityTerm.SupportedAt.congr hleft sourceSupported
  let innerCondLeft :=
    ProbabilityTerm.SupportedAt.congr hcond innerLeft
  ⟨sourceSupported,
    ⟨formulaSupported,
      ⟨innerLeft,
        ⟨formulaSupported,
          ⟨innerCondLeft, ⟨formulaSupported, ()⟩⟩⟩⟩⟩⟩

/-- The published certificate whose formula is Bayes' empty-action
reduction `P(Y, Z) / P(Z)`.  The ID engine further rewrites both
joints as observational marginals; that success-to-formula map is
`emptyActionIdentifiedConditionalIdDerivation`. -/
noncomputable def emptyActionPublishedConditionalCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    PublishedConditionalCertificate C correct q where
  formula :=
    .divide
      (.kernel ⟨NodeSet.union q.outcome q.condition,
        NodeSet.empty, NodeSet.empty⟩)
      (.kernel ⟨q.condition, NodeSet.empty, NodeSet.empty⟩)
  actionFree := by
    constructor
    · intro i; rfl
    · intro i; rfl
  derivation := emptyActionConditionalIdDerivation q emptyAction
  supported := fun model _member assignment sourceSupported =>
    emptyActionConditionalIdDerivation_supported correct q emptyAction
      model assignment sourceSupported
      (emptyActionConditionalBayes_supportedAt model q emptyAction
        assignment sourceSupported)

theorem identifyConditional_empty_action_succeeds
    (G : ObservedGraph S) (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    Legacy.identifyConditional G q =
      IdentificationOutcome.identified
        (.divide
          (.marginalize
            (NodeSet.diff NodeSet.full
              (NodeSet.union q.outcome q.condition))
            (observationalJointTerm S))
          (.marginalize
            (NodeSet.diff NodeSet.full q.condition)
            (observationalJointTerm S))) :=
  identifyConditional_of_empty_action G q emptyAction

/-- Successful empty-action IDC returns exactly the ID formula. -/
theorem emptyActionIdentifiedConditionalTerm_eq_identifyConditional
    (G : ObservedGraph S) (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true)
    {term : ProbabilityTerm S}
    (h : Legacy.identifyConditional G q = IdentificationOutcome.identified term) :
    term =
      .divide
        (.marginalize
          (NodeSet.diff NodeSet.full
            (NodeSet.union q.outcome q.condition))
          (observationalJointTerm S))
        (.marginalize
          (NodeSet.diff NodeSet.full q.condition)
          (observationalJointTerm S)) := by
  have hsucc := identifyConditional_empty_action_succeeds G q emptyAction
  rw [hsucc] at h
  injection h with hterm
  exact hterm.symm


/-- A finite sum of defined ancestral kernels `P(A)` is defined. -/
noncomputable def ancestralSliceMarginal_supportedAt
    (model : FiniteLatentSCM S) (A Y : NodeSet S)
    (assignment : S.Assignment) :
    (ProbabilityTerm.marginalize (NodeSet.diff A Y)
      (.kernel ⟨A, NodeSet.empty, NodeSet.empty⟩)).SupportedAt
      model assignment := by
  simpa [ProbabilityTerm.denote] using
    ProbabilityResult.sum_map_supported
      (ProbabilityTerm.marginalAssignments S (NodeSet.diff A Y) assignment)
      (fun variant =>
        (ProbabilityTerm.kernel
          ⟨A, NodeSet.empty, NodeSet.empty⟩).denote model variant)
      (fun variant => emptyActionKernel_supportedAt model A variant)

/-- Nested empty-action ID: `∑_{A \ Y} ∑_{V \ A} P(V)` is defined. -/
noncomputable def nestedAncestralMarginal_supportedAt
    (model : FiniteLatentSCM S) (A Y : NodeSet S)
    (assignment : S.Assignment) :
    (ProbabilityTerm.marginalize (NodeSet.diff A Y)
      (.marginalize (NodeSet.diff NodeSet.full A)
        (observationalJointTerm S))).SupportedAt model assignment := by
  simpa [ProbabilityTerm.denote] using
    ProbabilityResult.sum_map_supported
      (ProbabilityTerm.marginalAssignments S (NodeSet.diff A Y) assignment)
      (fun variant =>
        (ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full A)
          (observationalJointTerm S)).denote model variant)
      (fun variant => emptyActionMarginal_supportedAt model A variant)

/-- Support tree of empty-action ID on an unconditional kernel. -/
noncomputable def unconditionalEmptyActionIdDerivation_supported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (outcome : NodeSet S)
    (model : FiniteLatentSCM S) (assignment : S.Assignment) :
    LocalDerivationSupport model assignment
      ((unconditionalEmptyActionIdDerivation (G := G) outcome).compile
        correct) :=
  let kernelSupported :=
    emptyActionKernel_supportedAt model outcome assignment
  let identified :=
    emptyActionMarginal_supportedAt model outcome assignment
  let innerRight :=
    ProbabilityTerm.SupportedAt.congr
      (emptyActionMarginalizationTerm_eq_of outcome).symm identified
  ⟨kernelSupported, ⟨identified, ⟨kernelSupported, ⟨innerRight, ()⟩⟩⟩⟩

/-- Support of the ID formula
`(∑_{V \ (Y ∪ Z)} P(V)) / (∑_{V \ Z} P(V))`: transport Bayes support
along empty-action marginalization of both joints. -/
noncomputable def emptyActionIdentifiedConditional_supportedAt
    (model : FiniteLatentSCM S) (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true)
    (assignment : S.Assignment)
    (sourceSupported : q.sourceTerm.SupportedAt model assignment) :
    (ProbabilityTerm.divide
      (.marginalize
        (NodeSet.diff NodeSet.full
          (NodeSet.union q.outcome q.condition))
        (observationalJointTerm S))
      (.marginalize
        (NodeSet.diff NodeSet.full q.condition)
        (observationalJointTerm S))).SupportedAt model assignment :=
  let bayesSupported :=
    emptyActionConditionalBayes_supportedAt model q emptyAction
      assignment sourceSupported
  have hnum :=
    emptyActionKernel_equiv_fullMarginal model
      (NodeSet.union q.outcome q.condition) assignment
  have hden :=
    emptyActionKernel_equiv_fullMarginal model q.condition assignment
  have hdiv :
      ProbabilityTerm.EquivalentAt model
        (.divide
          (.kernel ⟨NodeSet.union q.outcome q.condition,
            NodeSet.empty, NodeSet.empty⟩)
          (.kernel ⟨q.condition, NodeSet.empty, NodeSet.empty⟩))
        (.divide
          (.marginalize
            (NodeSet.diff NodeSet.full
              (NodeSet.union q.outcome q.condition))
            (observationalJointTerm S))
          (.marginalize
            (NodeSet.diff NodeSet.full q.condition)
            (observationalJointTerm S)))
        assignment := by
    simpa [ProbabilityTerm.denote, observationalJointTerm] using
      ProbabilityResult.divide_congr hnum hden
  ProbabilityTerm.SupportedAt.of_equivalent hdiv bayesSupported

/-- The published certificate whose formula is the ID engine's empty-action
IDC output. -/
noncomputable def emptyActionIdentifiedPublishedConditionalCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    PublishedConditionalCertificate C correct q where
  formula :=
    .divide
      (.marginalize
        (NodeSet.diff NodeSet.full
          (NodeSet.union q.outcome q.condition))
        (observationalJointTerm S))
      (.marginalize
        (NodeSet.diff NodeSet.full q.condition)
        (observationalJointTerm S))
  actionFree := by
    exact ⟨observationalJointTerm_actionFree S,
      observationalJointTerm_actionFree S⟩
  derivation := emptyActionIdentifiedConditionalIdDerivation q emptyAction
  supported := fun model _member assignment sourceSupported =>
    let formulaSupported :=
      emptyActionIdentifiedConditional_supportedAt model q emptyAction
        assignment sourceSupported
    let bayesSupported :=
      emptyActionConditionalBayes_supportedAt model q emptyAction
        assignment sourceSupported
    let hleft :=
      ConditionalKernelQuery.sourceTerm_eq_of_empty_action q emptyAction
    let hcond :
        ProbabilityTerm.kernel
          ⟨q.outcome, NodeSet.empty, q.condition⟩ =
        ProbabilityTerm.kernel
          ⟨q.outcome, NodeSet.empty,
            NodeSet.union q.condition NodeSet.empty⟩ := by
      simp [NodeSet.union_empty_right]
    let innerLeft :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    let innerCondLeft :=
      ProbabilityTerm.SupportedAt.congr hcond innerLeft
    let numKernelSupported :=
      emptyActionKernel_supportedAt model
        (NodeSet.union q.outcome q.condition) assignment
    let numIdentified :=
      emptyActionMarginal_supportedAt model
        (NodeSet.union q.outcome q.condition) assignment
    let numInnerRight :=
      ProbabilityTerm.SupportedAt.congr
        (emptyActionMarginalizationTerm_eq_of
          (NodeSet.union q.outcome q.condition)).symm
        numIdentified
    let denKernelSupported :=
      emptyActionKernel_supportedAt model q.condition assignment
    let denIdentified :=
      emptyActionMarginal_supportedAt model q.condition assignment
    let denInnerRight :=
      ProbabilityTerm.SupportedAt.congr
        (emptyActionMarginalizationTerm_eq_of q.condition).symm
        denIdentified
    ⟨sourceSupported,
      ⟨formulaSupported,
        ⟨⟨sourceSupported,
            ⟨bayesSupported,
              ⟨innerLeft,
                ⟨bayesSupported,
                  ⟨innerCondLeft, ⟨bayesSupported, ()⟩⟩⟩⟩⟩⟩,
          ⟨bayesSupported,
            ⟨formulaSupported,
              ⟨⟨numKernelSupported,
                  ⟨numIdentified,
                    ⟨numKernelSupported, ⟨numInnerRight, ()⟩⟩⟩⟩,
                ⟨denKernelSupported,
                  ⟨denIdentified,
                    ⟨denKernelSupported, ⟨denInnerRight, ()⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/--
The published certificate whose formula is the ID engine's empty-action
output.  Unlike `emptyActionPublishedCertificate`, which reflects the
source kernel, this one is the success-to-formula map: `Legacy.identifyJoint`
returns this same marginal of `P(V)`.
-/
noncomputable def emptyActionIdentifiedPublishedCertificate {G : ObservedGraph S}
    {C : GraphModelClass G} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true) :
    PublishedJointCertificate C correct q where
  formula :=
    .marginalize (NodeSet.diff NodeSet.full q.outcome)
      (observationalJointTerm S)
  actionFree := observationalJointTerm_actionFree S
  derivation := emptyActionIdDerivation q emptyAction
  supported := fun model _member assignment sourceSupported =>
    let hleft :=
      JointKernelQuery.sourceTerm_eq_of_empty_action q emptyAction
    let hright := (emptyActionMarginalizationTerm_eq q).symm
    let innerLeft := ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    let identified :=
      emptyActionIdentifiedTerm_supportedAt model q assignment
    let innerRight := ProbabilityTerm.SupportedAt.congr hright identified
    ⟨sourceSupported, ⟨identified, ⟨innerLeft, ⟨innerRight, ()⟩⟩⟩⟩


/--
Rule 3 followed by empty-action ID: `P(Y | do(X)) = P(Y) = ∑_{V \ Y} P(V)`
whenever `Y ⊥ X` in `G_{\overline{X}}`.
-/
def deleteActionIdentifiedIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome q.action NodeSet.empty) :
    PathDoCalculusDerivation G q.sourceTerm
      (.marginalize (NodeSet.diff NodeSet.full q.outcome)
        (observationalJointTerm S)) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (deleteActionRule3Derivation q separated)
    (unconditionalEmptyActionIdDerivation q.outcome)

/--
Nonempty-action identification when the query outcome is d-separated from
the action in `G_{\overline{X}}`.  The formula is the same observational
marginal as empty-action ID.
-/
noncomputable def deleteActionIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome q.action NodeSet.empty) :
    PublishedJointCertificate C correct q where
  formula :=
    .marginalize (NodeSet.diff NodeSet.full q.outcome)
      (observationalJointTerm S)
  actionFree := observationalJointTerm_actionFree S
  derivation := deleteActionIdentifiedIdDerivation q separated
  supported := fun model _member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      deleteActionIdentifiedIdDerivation, deleteActionRule3Derivation]
    let pY :=
      emptyActionKernel_supportedAt model q.outcome assignment
    let formulaSupported :=
      emptyActionMarginal_supportedAt model q.outcome assignment
    let hleft := JointKernelQuery.sourceTerm_eq_rule3Left_empty_xw q
    let rule3LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    exact
      ⟨sourceSupported,
        ⟨formulaSupported,
          ⟨⟨sourceSupported,
              ⟨pY, ⟨rule3LeftSupported, ⟨pY, ()⟩⟩⟩⟩,
            unconditionalEmptyActionIdDerivation_supported correct
              q.outcome model assignment⟩⟩⟩

/--
An empty outcome is vacuously d-separated from the action, so rule 3
deletes `X` and empty-action ID writes `∑_V P(V)`.
-/
noncomputable def emptyOutcomeIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (emptyOutcome : NodeSet.isEmpty q.outcome = true) :
    PublishedJointCertificate C correct q :=
  deleteActionIdentifiedPublishedCertificate correct q
    (PathSpecification.PathDSeparated.of_isEmpty_left G
      (GraphMutilation.bar q.action) q.outcome q.action NodeSet.empty
      emptyOutcome)

/-- Empty-outcome ID writes the complementary sum as `∑_V P(V)`. -/
theorem emptyOutcomeIdentifiedTerm_eq
    (q : JointKernelQuery S)
    (emptyOutcome : NodeSet.isEmpty q.outcome = true) :
    ProbabilityTerm.marginalize (NodeSet.diff NodeSet.full q.outcome)
        (observationalJointTerm S) =
      ProbabilityTerm.marginalize NodeSet.full
        (observationalJointTerm S) := by
  have hy : q.outcome = NodeSet.empty :=
    NodeSet.eq_empty_of_isEmpty emptyOutcome
  simp [hy, NodeSet.diff_empty]

/--
Boolean d-separation in `G_{\overline{X}}` unpacks to the published
delete-action certificate.
-/
noncomputable def deleteActionIdentifiedPublishedCertificate?
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S) :
    Option (PublishedJointCertificate C correct q) :=
  if h : G.dSeparated (GraphMutilation.bar q.action) q.outcome q.action
      NodeSet.empty = true then
    some (deleteActionIdentifiedPublishedCertificate correct q
      (correct.pathDSeparated_of_dSeparated h))
  else
    none

theorem deleteActionIdentifiedPublishedCertificate?_isSome_iff
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S) :
    (deleteActionIdentifiedPublishedCertificate? (C := C) correct q).isSome =
      G.dSeparated (GraphMutilation.bar q.action) q.outcome q.action
        NodeSet.empty := by
  dsimp [deleteActionIdentifiedPublishedCertificate?]
  split
  · next h => exact h.symm
  · next h =>
      cases hb :
          G.dSeparated (GraphMutilation.bar q.action) q.outcome q.action
            NodeSet.empty with
      | true => exact False.elim (h hb)
      | false => rfl

/--
A joint identification certificate whenever the action is empty, the
outcome is empty, or `Y ⊥ X` in `G_{\overline{X}}`.
-/
noncomputable def identifiedPublishedCertificate?
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S) :
    Option (PublishedJointCertificate C correct q) :=
  if hact : NodeSet.isEmpty q.action = true then
    some (emptyActionIdentifiedPublishedCertificate correct q hact)
  else if hy : NodeSet.isEmpty q.outcome = true then
    some (emptyOutcomeIdentifiedPublishedCertificate correct q hy)
  else
    deleteActionIdentifiedPublishedCertificate? correct q

theorem identifiedPublishedCertificate?_isSome_of_empty_action
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (hact : NodeSet.isEmpty q.action = true) :
    (identifiedPublishedCertificate? (C := C) correct q).isSome = true := by
  simp [identifiedPublishedCertificate?, hact]

theorem identifiedPublishedCertificate?_isSome_of_empty_outcome
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (hy : NodeSet.isEmpty q.outcome = true) :
    (identifiedPublishedCertificate? (C := C) correct q).isSome = true := by
  simp [identifiedPublishedCertificate?, hy]
  split
  · rfl
  · rfl

theorem identifiedPublishedCertificate?_isSome_of_dSeparated
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (hsep : G.dSeparated (GraphMutilation.bar q.action) q.outcome q.action
      NodeSet.empty = true) :
    (identifiedPublishedCertificate? (C := C) correct q).isSome = true := by
  simp [identifiedPublishedCertificate?]
  split
  · rfl
  · split
    · rfl
    · simp [deleteActionIdentifiedPublishedCertificate?, hsep]

/-- Every joint packer certificate is the complementary observational
marginal of the query outcome. -/
theorem identifiedPublishedCertificate?_formula
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    {cert : PublishedJointCertificate C correct q}
    (h : identifiedPublishedCertificate? (C := C) correct q = some cert) :
    cert.formula =
      .marginalize (NodeSet.diff NodeSet.full q.outcome)
        (observationalJointTerm S) := by
  dsimp [identifiedPublishedCertificate?] at h
  split at h
  · next _ =>
      injection h with hcert
      subst hcert
      rfl
  · split at h
    · next _ =>
        injection h with hcert
        subst hcert
        rfl
    · dsimp [deleteActionIdentifiedPublishedCertificate?] at h
      split at h
      · next _ =>
          injection h with hcert
          subst hcert
          rfl
      · cases h


/--
Rule 2 with empty original action and empty given-set: the side graph is
`G_{\underline{Z}}` with empty conditioner.  Exchanging `Z` from
`P(Y | do(Z))` into `P(Y | Z)` is the underline d-separation of `Y`
from `Z`.
-/
theorem pathDSeparated_rule2_empty_xw
    (G : ObservedGraph S) (y z : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty z) y z NodeSet.empty) :
    PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline NodeSet.empty z) y z
      (NodeSet.union NodeSet.empty NodeSet.empty) := by
  simpa [NodeSet.union_empty_left] using separated

theorem JointKernelQuery.sourceTerm_eq_rule2Left_empty_xw
    (q : JointKernelQuery S) :
    q.sourceTerm =
      .kernel
        (rule2Left NodeSet.empty q.outcome q.action NodeSet.empty) := by
  simp [JointKernelQuery.sourceTerm, rule2Left, NodeSet.union_empty_left]

theorem JointKernelQuery.observationalCondition_eq_rule2Right_empty_xw
    (q : JointKernelQuery S) :
    ProbabilityTerm.kernel ⟨q.outcome, NodeSet.empty, q.action⟩ =
      .kernel
        (rule2Right NodeSet.empty q.outcome q.action NodeSet.empty) := by
  simp [rule2Right, NodeSet.union_empty_right]

/--
Rule 2 exchanges a nonempty action for an observation once `Y` is
path-d-separated from `X` in `G_{\underline{X}}`.  The right kernel is
the observational conditional `P(Y | X)`.
-/
def exchangeActionRule2Derivation {G : ObservedGraph S}
    (q : JointKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty) :
    PathDoCalculusDerivation G q.sourceTerm
      (.kernel ⟨q.outcome, NodeSet.empty, q.action⟩) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (JointKernelQuery.sourceTerm_eq_rule2Left_empty_xw q)
    (JointKernelQuery.observationalCondition_eq_rule2Right_empty_xw q)
    (DoCalculusDerivation.doRule
      (G := G) (separation := pathRuleSeparation G)
      (DoRuleApplication.rule2 (G := G) (separation := pathRuleSeparation G)
        NodeSet.empty q.outcome q.action NodeSet.empty
        (FourWayDisjoint.emptyActionConditioning q.outcome q.action
          q.outcome_action_disjoint)
        (pathDSeparated_rule2_empty_xw G q.outcome q.action separated)))

/--
Nonempty-action identification when the query outcome is d-separated from
the action in `G_{\underline{X}}`.  The formula is the observational
conditional `P(Y | X)`, defined in observationally positive models.
-/
noncomputable def exchangeActionIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (obsPositive :
      forall {model : ExactModel S}, C.Mem model ->
        ObservationallyPositive model)
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty) :
    PublishedJointCertificate C correct q where
  formula := .kernel ⟨q.outcome, NodeSet.empty, q.action⟩
  actionFree := by
    intro _i
    rfl
  derivation := exchangeActionRule2Derivation q separated
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      exchangeActionRule2Derivation]
    let formulaSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome q.action assignment
    let hleft := JointKernelQuery.sourceTerm_eq_rule2Left_empty_xw q
    let rule2LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    let hright :=
      JointKernelQuery.observationalCondition_eq_rule2Right_empty_xw q
    let rule2RightSupported :=
      ProbabilityTerm.SupportedAt.congr hright formulaSupported
    exact
      ⟨sourceSupported,
        ⟨formulaSupported,
          ⟨rule2LeftSupported, ⟨rule2RightSupported, ()⟩⟩⟩⟩

/-- Boolean underline d-separation unpacks to the observational
conditional certificate on the classical class. -/
noncomputable def exchangeActionIdentifiedPublishedCertificate?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  if h : G.dSeparated
      (GraphMutilation.barUnderline NodeSet.empty q.action) q.outcome
      q.action NodeSet.empty = true then
    some
      (exchangeActionIdentifiedPublishedCertificate
        (C := GraphModelClass.positive G)
        (fun {model} (member : (GraphModelClass.positive G).Mem model) =>
          member.2)
        correct q
        (correct.pathDSeparated_of_dSeparated h))
  else
    none

theorem exchangeActionIdentifiedPublishedCertificate?_formula
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    {cert : PublishedJointCertificate (GraphModelClass.positive G) correct q}
    (h : exchangeActionIdentifiedPublishedCertificate? correct q = some cert) :
    cert.formula =
      .kernel ⟨q.outcome, NodeSet.empty, q.action⟩ := by
  dsimp [exchangeActionIdentifiedPublishedCertificate?] at h
  split at h
  · next _hsep =>
      injection h with hcert
      subst hcert
      rfl
  · cases h

/-- Rest of the outcome after removing its earliest selected vertex. -/
def productSplitRest (q : JointKernelQuery S) (head : Fin S.count) :
    NodeSet S :=
  NodeSet.diff q.outcome (NodeSet.singleton head)

/-- The earliest selected vertex together with the rest recovers `Y`. -/
theorem productSplit_union_eq (q : JointKernelQuery S) {head : Fin S.count}
    (hhead : q.outcome head = true) :
    NodeSet.union (productSplitRest q head) (NodeSet.singleton head) =
      q.outcome :=
  NodeSet.diff_union_eq (NodeSet.singleton_subset_of_mem hhead)

/-- Empty-action four-way disjointness of the rest, the earliest vertex,
and the original action (now an observational conditioner). -/
def productSplitFourWay (q : JointKernelQuery S) {head : Fin S.count}
    (hhead : q.outcome head = true) :
    FourWayDisjoint NodeSet.empty (productSplitRest q head)
      (NodeSet.singleton head) q.action :=
  FourWayDisjoint.emptyAction
    (productSplitRest q head) (NodeSet.singleton head) q.action
    (NodeSet.disjoint_diff_right q.outcome (NodeSet.singleton head))
    (fun i hi =>
      q.outcome_action_disjoint i
        (NodeSet.diff_subset_left q.outcome (NodeSet.singleton head) i hi))
    (fun i hi =>
      q.outcome_action_disjoint i
        (NodeSet.singleton_subset_of_mem hhead i hi))

/-- Rule 1 with empty original action: the side-condition graph is `G`
itself (no incoming cut) with conditioner `W`. -/
theorem pathDSeparated_rule1_empty_x
    (G : ObservedGraph S) (y z w : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar NodeSet.empty)
        y z w) :
    PathSpecification.PathDSeparated G (GraphMutilation.bar NodeSet.empty)
      y z (NodeSet.union NodeSet.empty w) := by
  simpa [NodeSet.union_empty_left] using separated

theorem productSplit_observational_eq (q : JointKernelQuery S)
    {head : Fin S.count} (hhead : q.outcome head = true) :
    ProbabilityTerm.kernel ⟨q.outcome, NodeSet.empty, q.action⟩ =
      .kernel ⟨NodeSet.union (productSplitRest q head) (NodeSet.singleton head),
        NodeSet.empty, q.action⟩ := by
  rw [productSplit_union_eq q hhead]

theorem productSplit_formula_eq (q : JointKernelQuery S)
    (head : Fin S.count) :
    ProbabilityTerm.multiply
        (.kernel ⟨productSplitRest q head, NodeSet.empty, q.action⟩)
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, q.action⟩) =
      .multiply
        (.kernel ⟨productSplitRest q head, NodeSet.empty, q.action⟩)
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, q.action⟩) :=
  rfl

/-- Observational chain: `P(Y_rest ∪ {head} | X) = P(Y_rest | head, X) P(head | X)`. -/
def productSplitChainDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {head : Fin S.count}
    (hhead : q.outcome head = true) :
    PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.union (productSplitRest q head)
          (NodeSet.singleton head),
        NodeSet.empty, q.action⟩)
      (.multiply
        (.kernel ⟨productSplitRest q head, NodeSet.empty,
          NodeSet.union (NodeSet.singleton head) q.action⟩)
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, q.action⟩)) :=
  DoCalculusDerivation.chain
    (G := G) (separation := pathRuleSeparation G)
    NodeSet.empty (productSplitRest q head) (NodeSet.singleton head)
    q.action (productSplitFourWay q hhead)

/-- Rule 1 deletes the earliest outcome vertex from the rest's
conditioner once those blocks are path-d-separated given `X` in `G`. -/
def productSplitRule1Derivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {head : Fin S.count}
    (hhead : q.outcome head = true)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar NodeSet.empty)
        (productSplitRest q head) (NodeSet.singleton head) q.action) :
    PathDoCalculusDerivation G
      (.kernel ⟨productSplitRest q head, NodeSet.empty,
        NodeSet.union (NodeSet.singleton head) q.action⟩)
      (.kernel ⟨productSplitRest q head, NodeSet.empty, q.action⟩) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (show ProbabilityTerm.kernel
        ⟨productSplitRest q head, NodeSet.empty,
          NodeSet.union (NodeSet.singleton head) q.action⟩ =
        .kernel
          (rule1Left NodeSet.empty (productSplitRest q head)
            (NodeSet.singleton head) q.action) from
      rfl)
    (show ProbabilityTerm.kernel
        ⟨productSplitRest q head, NodeSet.empty, q.action⟩ =
        .kernel
          (rule1Right NodeSet.empty (productSplitRest q head)
            (NodeSet.singleton head) q.action) from
      rfl)
    (DoCalculusDerivation.doRule
      (G := G) (separation := pathRuleSeparation G)
      (DoRuleApplication.rule1 (G := G) (separation := pathRuleSeparation G)
        NodeSet.empty (productSplitRest q head) (NodeSet.singleton head)
        q.action (productSplitFourWay q hhead)
        (pathDSeparated_rule1_empty_x G (productSplitRest q head)
          (NodeSet.singleton head) q.action separated)))

/-- Factor `P(Y | X)` into `P(Y_rest | X) P(head | X)` by chain plus
rule 1. -/
def productSplitFactorDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {head : Fin S.count}
    (hhead : q.outcome head = true)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar NodeSet.empty)
        (productSplitRest q head) (NodeSet.singleton head) q.action) :
    PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.union (productSplitRest q head)
          (NodeSet.singleton head),
        NodeSet.empty, q.action⟩)
      (.multiply
        (.kernel ⟨productSplitRest q head, NodeSet.empty, q.action⟩)
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, q.action⟩)) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (productSplitChainDerivation q hhead)
    (DoCalculusDerivation.multiplyCongr
      (G := G) (separation := pathRuleSeparation G)
      (productSplitRule1Derivation q hhead separated)
      (DoCalculusDerivation.refl
        (G := G) (separation := pathRuleSeparation G)
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, q.action⟩)))

/-- Exchange `do(X)` for an observation, then factor the observational
conditional across a d-separated split of the outcome. -/
def productSplitIdentifiedIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {head : Fin S.count}
    (hhead : q.outcome head = true)
    (separatedExchange :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (separatedSplit :
      PathSpecification.PathDSeparated G (GraphMutilation.bar NodeSet.empty)
        (productSplitRest q head) (NodeSet.singleton head) q.action) :
    PathDoCalculusDerivation G q.sourceTerm
      (.multiply
        (.kernel ⟨productSplitRest q head, NodeSet.empty, q.action⟩)
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, q.action⟩)) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (exchangeActionRule2Derivation q separatedExchange)
    (DoCalculusDerivation.eqCongr
      (G := G) (separation := pathRuleSeparation G)
      (productSplit_observational_eq q hhead)
      (productSplit_formula_eq q head)
      (productSplitFactorDerivation q hhead separatedSplit))

/--
Independent product-split of a composite outcome: after rule 2 writes
`P(Y | X)`, chain plus rule 1 factor `P(Y_rest | X) P(head | X)` once
the earliest outcome vertex is path-d-separated from the rest given
`X` in `G`.  Both factors are observational conditionals, so the
formula is defined in every observationally positive model.
-/
noncomputable def productSplitIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (obsPositive :
      forall {model : ExactModel S}, C.Mem model ->
        ObservationallyPositive model)
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    {head : Fin S.count} (hhead : q.outcome head = true)
    (separatedExchange :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (separatedSplit :
      PathSpecification.PathDSeparated G (GraphMutilation.bar NodeSet.empty)
        (productSplitRest q head) (NodeSet.singleton head) q.action) :
    PublishedJointCertificate C correct q where
  formula :=
    .multiply
      (.kernel ⟨productSplitRest q head, NodeSet.empty, q.action⟩)
      (.kernel ⟨NodeSet.singleton head, NodeSet.empty, q.action⟩)
  actionFree := by
    constructor
    · intro _i; rfl
    · intro _i; rfl
  derivation :=
    productSplitIdentifiedIdDerivation q hhead separatedExchange
      separatedSplit
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      productSplitIdentifiedIdDerivation, exchangeActionRule2Derivation,
      productSplitFactorDerivation, productSplitChainDerivation,
      productSplitRule1Derivation]
    let rest := productSplitRest q head
    let pyxSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome q.action assignment
    let restGivenHeadSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        rest (NodeSet.union (NodeSet.singleton head) q.action) assignment
    let headSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        (NodeSet.singleton head) q.action assignment
    let restSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        rest q.action assignment
    have formulaSupported :
        (ProbabilityTerm.multiply
          (.kernel ⟨productSplitRest q head, NodeSet.empty, q.action⟩)
          (.kernel ⟨NodeSet.singleton head, NodeSet.empty, q.action⟩)).SupportedAt
          model assignment := by
      simpa [ProbabilityTerm.denote] using
        ProbabilityResult.multiply_supported restSupported headSupported
    let unionSupported :=
      ProbabilityTerm.SupportedAt.congr
        (productSplit_observational_eq q hhead) pyxSupported
    have chainRightSupported :
        (ProbabilityTerm.multiply
          (.kernel ⟨productSplitRest q head, NodeSet.empty,
            NodeSet.union (NodeSet.singleton head) q.action⟩)
          (.kernel ⟨NodeSet.singleton head, NodeSet.empty, q.action⟩)).SupportedAt
          model assignment := by
      simpa [ProbabilityTerm.denote] using
        ProbabilityResult.multiply_supported restGivenHeadSupported
          headSupported
    let hleft := JointKernelQuery.sourceTerm_eq_rule2Left_empty_xw q
    let rule2LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    let hright :=
      JointKernelQuery.observationalCondition_eq_rule2Right_empty_xw q
    let rule2RightSupported :=
      ProbabilityTerm.SupportedAt.congr hright pyxSupported
    let exchangeSupported :
        LocalDerivationSupport model assignment
          ((exchangeActionRule2Derivation q separatedExchange).compile
            correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        exchangeActionRule2Derivation]
      exact
        ⟨sourceSupported,
          ⟨pyxSupported,
            ⟨rule2LeftSupported, ⟨rule2RightSupported, ()⟩⟩⟩⟩
    let factorSupported :
        LocalDerivationSupport model assignment
          ((productSplitFactorDerivation q hhead separatedSplit).compile
            correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        productSplitFactorDerivation, productSplitChainDerivation,
        productSplitRule1Derivation]
      exact
        ⟨unionSupported,
          ⟨formulaSupported,
            ⟨⟨unionSupported, ⟨chainRightSupported, ()⟩⟩,
              ⟨chainRightSupported,
                ⟨formulaSupported,
                  ⟨⟨restGivenHeadSupported,
                      ⟨restSupported,
                        ⟨restGivenHeadSupported,
                          ⟨restSupported, ()⟩⟩⟩⟩,
                    ⟨headSupported, ⟨headSupported, ()⟩⟩⟩⟩⟩⟩⟩⟩
    exact
      ⟨sourceSupported,
        ⟨formulaSupported,
          ⟨exchangeSupported,
            ⟨pyxSupported, ⟨formulaSupported, factorSupported⟩⟩⟩⟩⟩

/-- Boolean product-split: at least two outcome vertices, underline
d-separation of `Y` from `X`, and bar-empty d-separation of the rest
from the earliest vertex given `X`. -/
noncomputable def productSplitIdentifiedPublishedCertificate?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  match hmem : NodeSet.members q.outcome with
  | [] => none
  | [_] => none
  | head :: _ :: _ =>
      let hhead : q.outcome head = true := NodeSet.mem_of_members_cons hmem
      if hex : G.dSeparated
          (GraphMutilation.barUnderline NodeSet.empty q.action)
          q.outcome q.action NodeSet.empty = true then
        if hind : G.dSeparated (GraphMutilation.bar NodeSet.empty)
            (productSplitRest q head) (NodeSet.singleton head)
            q.action = true then
          some
            (productSplitIdentifiedPublishedCertificate
              (C := GraphModelClass.positive G)
              (fun {model}
                  (member : (GraphModelClass.positive G).Mem model) =>
                member.2)
              correct q hhead
              (correct.pathDSeparated_of_dSeparated hex)
              (correct.pathDSeparated_of_dSeparated hind))
        else
          none
      else
        none

/-- Earliest-versus-rest cut of an arbitrary outcome block. -/
def splitRest (nodes : NodeSet S) (head : Fin S.count) : NodeSet S :=
  NodeSet.diff nodes (NodeSet.singleton head)

/-- Empty-action four-way disjointness of a peeled outcome block against
its observational conditioner. -/
def observationalSplitFourWay (nodes condition : NodeSet S)
    {head : Fin S.count} (hhead : nodes head = true)
    (hdis : NodeSet.Disjoint nodes condition) :
    FourWayDisjoint NodeSet.empty (splitRest nodes head)
      (NodeSet.singleton head) condition :=
  FourWayDisjoint.emptyAction
    (splitRest nodes head) (NodeSet.singleton head) condition
    (NodeSet.disjoint_diff_right nodes (NodeSet.singleton head))
    (fun i hi =>
      hdis i (NodeSet.diff_subset_left nodes (NodeSet.singleton head) i hi))
    (fun i hi =>
      hdis i (NodeSet.singleton_subset_of_mem hhead i hi))

theorem observationalSplit_union_eq (nodes : NodeSet S) {head : Fin S.count}
    (hhead : nodes head = true) :
    NodeSet.union (splitRest nodes head) (NodeSet.singleton head) = nodes :=
  NodeSet.diff_union_eq (NodeSet.singleton_subset_of_mem hhead)

def observationalSplitChainDerivation {G : ObservedGraph S}
    (nodes condition : NodeSet S) {head : Fin S.count}
    (hhead : nodes head = true)
    (hdis : NodeSet.Disjoint nodes condition) :
    PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.union (splitRest nodes head) (NodeSet.singleton head),
        NodeSet.empty, condition⟩)
      (.multiply
        (.kernel ⟨splitRest nodes head, NodeSet.empty,
          NodeSet.union (NodeSet.singleton head) condition⟩)
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, condition⟩)) :=
  DoCalculusDerivation.chain
    (G := G) (separation := pathRuleSeparation G)
    NodeSet.empty (splitRest nodes head) (NodeSet.singleton head)
    condition (observationalSplitFourWay nodes condition hhead hdis)

def observationalSplitRule1Derivation {G : ObservedGraph S}
    (nodes condition : NodeSet S) {head : Fin S.count}
    (hhead : nodes head = true)
    (hdis : NodeSet.Disjoint nodes condition)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar NodeSet.empty)
        (splitRest nodes head) (NodeSet.singleton head) condition) :
    PathDoCalculusDerivation G
      (.kernel ⟨splitRest nodes head, NodeSet.empty,
        NodeSet.union (NodeSet.singleton head) condition⟩)
      (.kernel ⟨splitRest nodes head, NodeSet.empty, condition⟩) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    rfl rfl
    (DoCalculusDerivation.doRule
      (G := G) (separation := pathRuleSeparation G)
      (DoRuleApplication.rule1 (G := G) (separation := pathRuleSeparation G)
        NodeSet.empty (splitRest nodes head) (NodeSet.singleton head)
        condition (observationalSplitFourWay nodes condition hhead hdis)
        (pathDSeparated_rule1_empty_x G (splitRest nodes head)
          (NodeSet.singleton head) condition separated)))

def observationalSplitFactorDerivation {G : ObservedGraph S}
    (nodes condition : NodeSet S) {head : Fin S.count}
    (hhead : nodes head = true)
    (hdis : NodeSet.Disjoint nodes condition)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar NodeSet.empty)
        (splitRest nodes head) (NodeSet.singleton head) condition) :
    PathDoCalculusDerivation G
      (.kernel ⟨NodeSet.union (splitRest nodes head) (NodeSet.singleton head),
        NodeSet.empty, condition⟩)
      (.multiply
        (.kernel ⟨splitRest nodes head, NodeSet.empty, condition⟩)
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, condition⟩)) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (observationalSplitChainDerivation nodes condition hhead hdis)
    (DoCalculusDerivation.multiplyCongr
      (G := G) (separation := pathRuleSeparation G)
      (observationalSplitRule1Derivation nodes condition hhead hdis separated)
      (DoCalculusDerivation.refl
        (G := G) (separation := pathRuleSeparation G)
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, condition⟩)))

/-- Fully factored observational product along a member list, later
blocks first so the chain constructor does not need multiply-comm. -/
def productSplitAllTermFrom (condition : NodeSet S) :
    List (Fin S.count) -> ProbabilityTerm S
  | [] =>
      .kernel ⟨NodeSet.empty, NodeSet.empty, condition⟩
  | [j] =>
      .kernel ⟨NodeSet.singleton j, NodeSet.empty, condition⟩
  | head :: t :: rest =>
      .multiply
        (productSplitAllTermFrom condition (t :: rest))
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, condition⟩)

/-- Fully factored observational product `∏_v P(v | X)` along `members`. -/
def productSplitAllTerm (nodes condition : NodeSet S) : ProbabilityTerm S :=
  productSplitAllTermFrom condition (NodeSet.members nodes)

theorem productSplitAllTermFrom_nil (condition : NodeSet S) :
    productSplitAllTermFrom condition [] =
      .kernel ⟨NodeSet.empty, NodeSet.empty, condition⟩ :=
  rfl

theorem productSplitAllTermFrom_one (condition : NodeSet S)
    (j : Fin S.count) :
    productSplitAllTermFrom condition [j] =
      .kernel ⟨NodeSet.singleton j, NodeSet.empty, condition⟩ :=
  rfl

theorem productSplitAllTermFrom_succ (condition : NodeSet S)
    (head t : Fin S.count) (rest : List (Fin S.count)) :
    productSplitAllTermFrom condition (head :: t :: rest) =
      .multiply
        (productSplitAllTermFrom condition (t :: rest))
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, condition⟩) :=
  rfl

theorem productSplitAllTerm_eq_one (nodes condition : NodeSet S)
    {j : Fin S.count} (hmem : NodeSet.members nodes = [j]) :
    productSplitAllTerm nodes condition =
      .kernel ⟨NodeSet.singleton j, NodeSet.empty, condition⟩ := by
  unfold productSplitAllTerm
  rw [hmem]
  rfl

theorem productSplitAllTerm_eq_succ (nodes condition : NodeSet S)
    {head t : Fin S.count} {rest : List (Fin S.count)}
    (hmem : NodeSet.members nodes = head :: t :: rest) :
    productSplitAllTerm nodes condition =
      .multiply
        (productSplitAllTermFrom condition (t :: rest))
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, condition⟩) := by
  unfold productSplitAllTerm
  rw [hmem]
  rfl

theorem productSplitAllTermFrom_eq_rest (nodes condition : NodeSet S)
    {head t : Fin S.count} {rest : List (Fin S.count)}
    (hmem : NodeSet.members nodes = head :: t :: rest) :
    productSplitAllTermFrom condition (t :: rest) =
      productSplitAllTerm (splitRest nodes head) condition := by
  simp [productSplitAllTerm, splitRest, NodeSet.members_diff_of_cons hmem]

theorem productSplitAllTerm_eq_succ_rest (nodes condition : NodeSet S)
    {head t : Fin S.count} {rest : List (Fin S.count)}
    (hmem : NodeSet.members nodes = head :: t :: rest) :
    productSplitAllTerm nodes condition =
      .multiply
        (productSplitAllTerm (splitRest nodes head) condition)
        (.kernel ⟨NodeSet.singleton head, NodeSet.empty, condition⟩) :=
  (productSplitAllTerm_eq_succ nodes condition hmem).trans
    (congrArg (fun inner =>
        ProbabilityTerm.multiply inner
          (.kernel ⟨NodeSet.singleton head, NodeSet.empty, condition⟩))
      (productSplitAllTermFrom_eq_rest nodes condition hmem))

theorem productSplitAllTermFrom_actionFree (condition : NodeSet S) :
    forall nodes, (productSplitAllTermFrom condition nodes).ActionFree
  | [] => fun _i => rfl
  | [_] => fun _i => rfl
  | _head :: _t :: _rest =>
      ⟨productSplitAllTermFrom_actionFree condition _, fun _i => rfl⟩

theorem productSplitAllTerm_actionFree (nodes condition : NodeSet S) :
    (productSplitAllTerm nodes condition).ActionFree :=
  productSplitAllTermFrom_actionFree condition _

/-- Successive rest-versus-head d-separation tests along a member list. -/
def successiveSplitOkFrom (G : ObservedGraph S)
    (nodes condition : NodeSet S) : List (Fin S.count) -> Bool
  | [] => true
  | [_] => true
  | head :: t :: rest =>
      G.dSeparated (GraphMutilation.bar NodeSet.empty)
        (splitRest nodes head) (NodeSet.singleton head) condition &&
      successiveSplitOkFrom G (splitRest nodes head) condition (t :: rest)

/-- Successive rest-versus-head d-separation tests along `members`. -/
def successiveSplitOk (G : ObservedGraph S)
    (nodes condition : NodeSet S) : Bool :=
  successiveSplitOkFrom G nodes condition (NodeSet.members nodes)

theorem successiveSplitOk_eq_succ {G : ObservedGraph S}
    (nodes condition : NodeSet S)
    {head t : Fin S.count} {rest : List (Fin S.count)}
    (hmem : NodeSet.members nodes = head :: t :: rest) :
    successiveSplitOk G nodes condition =
      (G.dSeparated (GraphMutilation.bar NodeSet.empty)
        (splitRest nodes head) (NodeSet.singleton head) condition &&
        successiveSplitOk G (splitRest nodes head) condition) := by
  unfold successiveSplitOk
  rw [hmem]
  simp [successiveSplitOkFrom]
  have hrest : NodeSet.members (splitRest nodes head) = t :: rest := by
    simpa [splitRest] using NodeSet.members_diff_of_cons hmem
  rw [hrest]

theorem members_splitRest_of_cons (nodes : NodeSet S)
    {head t : Fin S.count} {rest : List (Fin S.count)}
    (hmem : NodeSet.members nodes = head :: t :: rest) :
    NodeSet.members (splitRest nodes head) = t :: rest := by
  simpa [splitRest] using NodeSet.members_diff_of_cons hmem

theorem successiveSplitOkFrom_dSeparated {G : ObservedGraph S}
    {nodes condition : NodeSet S} {head t : Fin S.count}
    {rest : List (Fin S.count)}
    (hok : successiveSplitOkFrom G nodes condition (head :: t :: rest) = true) :
    G.dSeparated (GraphMutilation.bar NodeSet.empty)
      (splitRest nodes head) (NodeSet.singleton head) condition = true :=
  (Bool.and_eq_true_iff.mp (by simpa [successiveSplitOkFrom] using hok)).1

theorem successiveSplitOkFrom_tail {G : ObservedGraph S}
    {nodes condition : NodeSet S} {head t : Fin S.count}
    {rest : List (Fin S.count)}
    (hok : successiveSplitOkFrom G nodes condition (head :: t :: rest) = true) :
    successiveSplitOkFrom G (splitRest nodes head) condition (t :: rest) = true :=
  (Bool.and_eq_true_iff.mp (by simpa [successiveSplitOkFrom] using hok)).2


theorem observationalSplit_kernel_eq (nodes condition : NodeSet S)
    {head : Fin S.count} (hhead : nodes head = true) :
    ProbabilityTerm.kernel ⟨nodes, NodeSet.empty, condition⟩ =
      .kernel ⟨NodeSet.union (splitRest nodes head) (NodeSet.singleton head),
        NodeSet.empty, condition⟩ := by
  rw [observationalSplit_union_eq nodes hhead]

theorem isEmpty_of_members_nil {X : NodeSet S}
    (h : NodeSet.members X = []) : NodeSet.isEmpty X = true := by
  unfold NodeSet.isEmpty
  simp [h]

/-- Empty observational block: `P(∅ | X)`. -/
def productSplitAllDerivation_nil {G : ObservedGraph S}
    (nodes condition : NodeSet S)
    (hmem : NodeSet.members nodes = []) :
    PathDoCalculusDerivation G
      (.kernel ⟨nodes, NodeSet.empty, condition⟩)
      (productSplitAllTermFrom condition []) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (congrArg (fun y => ProbabilityTerm.kernel ⟨y, NodeSet.empty, condition⟩)
      (NodeSet.eq_empty_of_isEmpty (isEmpty_of_members_nil hmem)))
    (productSplitAllTermFrom_nil condition)
    (DoCalculusDerivation.refl
      (G := G) (separation := pathRuleSeparation G)
      (.kernel ⟨NodeSet.empty, NodeSet.empty, condition⟩))

/-- Singleton observational block: `P({j} | X)` after `Y = {j}`. -/
def productSplitAllDerivation_one {G : ObservedGraph S}
    (nodes condition : NodeSet S) {j : Fin S.count}
    (hmem : NodeSet.members nodes = [j]) :
    PathDoCalculusDerivation G
      (.kernel ⟨nodes, NodeSet.empty, condition⟩)
      (productSplitAllTermFrom condition [j]) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (congrArg (fun y => ProbabilityTerm.kernel ⟨y, NodeSet.empty, condition⟩)
      (NodeSet.eq_singleton_of_members hmem))
    (productSplitAllTermFrom_one condition j)
    (DoCalculusDerivation.refl
      (G := G) (separation := pathRuleSeparation G)
      (.kernel ⟨NodeSet.singleton j, NodeSet.empty, condition⟩))

/-- One peel: factor the earliest vertex, then recurse on the rest
list.  The inner derivation is already the fully factored product of
the remaining members. -/
def productSplitAllDerivation_succ {G : ObservedGraph S}
    (nodes condition : NodeSet S) {head t : Fin S.count}
    {rest : List (Fin S.count)}
    (hmem : NodeSet.members nodes = head :: t :: rest)
    (hdis : NodeSet.Disjoint nodes condition)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar NodeSet.empty)
        (splitRest nodes head) (NodeSet.singleton head) condition)
    (inner :
      PathDoCalculusDerivation G
        (.kernel ⟨splitRest nodes head, NodeSet.empty, condition⟩)
        (productSplitAllTermFrom condition (t :: rest))) :
    PathDoCalculusDerivation G
      (.kernel ⟨nodes, NodeSet.empty, condition⟩)
      (productSplitAllTermFrom condition (head :: t :: rest)) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (observationalSplit_kernel_eq nodes condition
      (NodeSet.mem_of_members_cons hmem))
    (productSplitAllTermFrom_succ condition head t rest)
    (DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G)
      (observationalSplitFactorDerivation nodes condition
        (NodeSet.mem_of_members_cons hmem) hdis separated)
      (DoCalculusDerivation.multiplyCongr
        (G := G) (separation := pathRuleSeparation G)
        inner
        (DoCalculusDerivation.refl
          (G := G) (separation := pathRuleSeparation G)
          (.kernel ⟨NodeSet.singleton head, NodeSet.empty, condition⟩))))

/-- Recursively factor `P(Y | X)` along a member list. Empty and
singleton blocks are observational kernels; longer blocks peel the
earliest member. Structural recursion on the list, so the inner rest
is a subterm. -/
def productSplitAllDerivationFrom {G : ObservedGraph S}
    (correct : DSeparationCorrectness G)
    (nodes condition : NodeSet S)
    (hdis : NodeSet.Disjoint nodes condition) :
    (members : List (Fin S.count)) →
    (hmem : NodeSet.members nodes = members) →
    (hok : successiveSplitOkFrom G nodes condition members = true) →
    PathDoCalculusDerivation G
      (.kernel ⟨nodes, NodeSet.empty, condition⟩)
      (productSplitAllTermFrom condition members)
  | [], hmem, _hok =>
      productSplitAllDerivation_nil nodes condition hmem
  | [_], hmem, _hok =>
      productSplitAllDerivation_one nodes condition hmem
  | head :: t :: rest, hmem, hok =>
      productSplitAllDerivation_succ nodes condition hmem hdis
        (correct.pathDSeparated_of_dSeparated
          (successiveSplitOkFrom_dSeparated hok))
        (productSplitAllDerivationFrom correct (splitRest nodes head)
          condition
          (fun i hi =>
            hdis i
              (NodeSet.diff_subset_left nodes (NodeSet.singleton head) i hi))
          (t :: rest) (members_splitRest_of_cons nodes hmem)
          (successiveSplitOkFrom_tail hok))

/-- Recursively factor `P(Y | X)` along successive rest-versus-head
d-separations. Empty and singleton blocks are observational kernels;
longer blocks peel the earliest member. -/
def productSplitAllDerivation {G : ObservedGraph S}
    (correct : DSeparationCorrectness G)
    (nodes condition : NodeSet S)
    (hdis : NodeSet.Disjoint nodes condition)
    (hok : successiveSplitOk G nodes condition = true) :
    PathDoCalculusDerivation G
      (.kernel ⟨nodes, NodeSet.empty, condition⟩)
      (productSplitAllTerm nodes condition) :=
  productSplitAllDerivationFrom correct nodes condition hdis
    (NodeSet.members nodes) rfl (by simpa [successiveSplitOk] using hok)

/-- Fully factored observational product is defined: every factor is an
observational conditional. -/
noncomputable def productSplitAllTermFrom_supportedAt
    {model : FiniteLatentSCM S} (positive : ObservationallyPositive model)
    (condition : NodeSet S) (assignment : S.Assignment) :
    forall members,
      (productSplitAllTermFrom condition members).SupportedAt model assignment
  | [] =>
      observationalConditional_supportedAt model positive
        NodeSet.empty condition assignment
  | [j] =>
      observationalConditional_supportedAt model positive
        (NodeSet.singleton j) condition assignment
  | head :: t :: rest =>
      ProbabilityTerm.multiply_supportedAt
        (productSplitAllTermFrom_supportedAt positive condition assignment
          (t :: rest))
        (observationalConditional_supportedAt model positive
          (NodeSet.singleton head) condition assignment)

noncomputable def productSplitAllTerm_supportedAt
    {model : FiniteLatentSCM S} (positive : ObservationallyPositive model)
    (nodes condition : NodeSet S) (assignment : S.Assignment) :
    (productSplitAllTerm nodes condition).SupportedAt model assignment :=
  productSplitAllTermFrom_supportedAt positive condition assignment
    (NodeSet.members nodes)

/-- The fully factored observational product is strictly positive:
each factor is an observational kernel whose numerator cylinder is
positive. -/
theorem productSplitAllTermFrom_num_pos
    {model : FiniteLatentSCM S} (positive : ObservationallyPositive model)
    (condition : NodeSet S) (assignment : S.Assignment) :
    forall members,
      0 <
        (productSplitAllTermFrom_supportedAt positive condition assignment
          members).1.num
  | [] =>
      observationalConditional_num_pos model positive NodeSet.empty
        condition assignment
  | [j] =>
      observationalConditional_num_pos model positive
        (NodeSet.singleton j) condition assignment
  | head :: t :: rest => by
      have hleft :=
        productSplitAllTermFrom_num_pos positive condition assignment
          (t :: rest)
      have hright :=
        observationalConditional_num_pos model positive
          (NodeSet.singleton head) condition assignment
      let inner :=
        productSplitAllTermFrom_supportedAt positive condition assignment
          (t :: rest)
      let headSup :=
        observationalConditional_supportedAt model positive
          (NodeSet.singleton head) condition assignment
      let hexpected :=
        ProbabilityResult.multiply_supported inner headSup
      have hposMul : 0 < hexpected.1.num := by
        have hvals :
            ProbabilityResult.Equivalent (some hexpected.1)
              (some (QProb.mul inner.1 headSup.1)) :=
          ProbabilityResult.trans (ProbabilityResult.symm hexpected.2)
            (ProbabilityResult.multiply_congr inner.2 headSup.2)
        cases hvals with
        | value hequiv =>
            exact
              (QProb.equiv_num_pos_iff hequiv).mpr (Nat.mul_pos hleft hright)
      let hmul :=
        productSplitAllTermFrom_supportedAt positive condition assignment
          (head :: t :: rest)
      cases ProbabilityResult.trans (ProbabilityResult.symm hmul.2)
          hexpected.2 with
      | value hequiv =>
          exact (QProb.equiv_num_pos_iff hequiv).mpr hposMul

theorem productSplitAllTerm_num_pos
    {model : FiniteLatentSCM S} (positive : ObservationallyPositive model)
    (nodes condition : NodeSet S) (assignment : S.Assignment) :
    0 <
      (productSplitAllTerm_supportedAt positive nodes condition
        assignment).1.num :=
  productSplitAllTermFrom_num_pos positive condition assignment
    (NodeSet.members nodes)

/-- Support tree of chain plus rule 1 for one observational peel. -/
noncomputable def observationalSplitFactorSupported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    {model : FiniteLatentSCM S} (positive : ObservationallyPositive model)
    (nodes condition : NodeSet S) {head : Fin S.count}
    (hhead : nodes head = true)
    (hdis : NodeSet.Disjoint nodes condition)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar NodeSet.empty)
        (splitRest nodes head) (NodeSet.singleton head) condition)
    (assignment : S.Assignment) :
    LocalDerivationSupport model assignment
      ((observationalSplitFactorDerivation nodes condition hhead hdis
          separated).compile correct) := by
  let rest := splitRest nodes head
  let unionSupported :=
    observationalConditional_supportedAt model positive
      (NodeSet.union rest (NodeSet.singleton head)) condition assignment
  let restGivenHeadSupported :=
    observationalConditional_supportedAt model positive rest
      (NodeSet.union (NodeSet.singleton head) condition) assignment
  let headSupported :=
    observationalConditional_supportedAt model positive
      (NodeSet.singleton head) condition assignment
  let restSupported :=
    observationalConditional_supportedAt model positive rest condition
      assignment
  let formulaSupported :=
    ProbabilityTerm.multiply_supportedAt restSupported headSupported
  let chainRightSupported :=
    ProbabilityTerm.multiply_supportedAt restGivenHeadSupported headSupported
  dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
    observationalSplitFactorDerivation, observationalSplitChainDerivation,
    observationalSplitRule1Derivation]
  exact
    ⟨unionSupported,
      ⟨formulaSupported,
        ⟨⟨unionSupported, ⟨chainRightSupported, ()⟩⟩,
          ⟨chainRightSupported,
            ⟨formulaSupported,
              ⟨⟨restGivenHeadSupported,
                  ⟨restSupported,
                    ⟨restGivenHeadSupported, ⟨restSupported, ()⟩⟩⟩⟩,
                ⟨headSupported, ⟨headSupported, ()⟩⟩⟩⟩⟩⟩⟩⟩

/-- Recursive support tree of `productSplitAllDerivationFrom`. -/
noncomputable def productSplitAllSupportedFrom
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    {model : FiniteLatentSCM S} (positive : ObservationallyPositive model)
    (nodes condition : NodeSet S)
    (hdis : NodeSet.Disjoint nodes condition)
    (assignment : S.Assignment) :
    (members : List (Fin S.count)) →
    (hmem : NodeSet.members nodes = members) →
    (hok : successiveSplitOkFrom G nodes condition members = true) →
    LocalDerivationSupport model assignment
      ((productSplitAllDerivationFrom correct nodes condition hdis members
          hmem hok).compile correct)
  | [], hmem, hok =>
      let emptySupported :=
        observationalConditional_supportedAt model positive
          NodeSet.empty condition assignment
      let nodesSupported :=
        ProbabilityTerm.SupportedAt.congr
          (congrArg
            (fun y => ProbabilityTerm.kernel ⟨y, NodeSet.empty, condition⟩)
            (NodeSet.eq_empty_of_isEmpty (isEmpty_of_members_nil hmem))).symm
          emptySupported
      let fromSupported :=
        productSplitAllTermFrom_supportedAt positive condition assignment []
      let supportNil :
          LocalDerivationSupport model assignment
            ((productSplitAllDerivation_nil (G := G) nodes condition
                hmem).compile correct) := by
        dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
          productSplitAllDerivation_nil]
        exact
          ⟨nodesSupported,
            ⟨fromSupported, ⟨emptySupported, ⟨emptySupported, ()⟩⟩⟩⟩
      have hder :
          productSplitAllDerivationFrom correct nodes condition hdis [] hmem
            hok =
            productSplitAllDerivation_nil (G := G) nodes condition hmem := by
        simp [productSplitAllDerivationFrom]
      hder ▸ supportNil
  | [j], hmem, hok =>
      let singletonSupported :=
        observationalConditional_supportedAt model positive
          (NodeSet.singleton j) condition assignment
      let nodesSupported :=
        ProbabilityTerm.SupportedAt.congr
          (congrArg
            (fun y => ProbabilityTerm.kernel ⟨y, NodeSet.empty, condition⟩)
            (NodeSet.eq_singleton_of_members hmem)).symm
          singletonSupported
      let fromSupported :=
        productSplitAllTermFrom_supportedAt positive condition assignment [j]
      let supportOne :
          LocalDerivationSupport model assignment
            ((productSplitAllDerivation_one (G := G) nodes condition
                hmem).compile correct) := by
        dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
          productSplitAllDerivation_one]
        exact
          ⟨nodesSupported,
            ⟨fromSupported,
              ⟨singletonSupported, ⟨singletonSupported, ()⟩⟩⟩⟩
      have hder :
          productSplitAllDerivationFrom correct nodes condition hdis [j] hmem
            hok =
            productSplitAllDerivation_one (G := G) nodes condition hmem := by
        simp [productSplitAllDerivationFrom]
      hder ▸ supportOne
  | head :: t :: rest, hmem, hok =>
      let hhead : nodes head = true := NodeSet.mem_of_members_cons hmem
      let nodesSupported :=
        observationalConditional_supportedAt model positive nodes condition
          assignment
      let unionSupported :=
        ProbabilityTerm.SupportedAt.congr
          (observationalSplit_kernel_eq nodes condition hhead) nodesSupported
      let restKernelSupported :=
        observationalConditional_supportedAt model positive
          (splitRest nodes head) condition assignment
      let headSupported :=
        observationalConditional_supportedAt model positive
          (NodeSet.singleton head) condition assignment
      let fromSupported :=
        productSplitAllTermFrom_supportedAt positive condition assignment
          (head :: t :: rest)
      let kernelMultiplySupported :=
        ProbabilityTerm.multiply_supportedAt restKernelSupported headSupported
      let factorSupported :=
        observationalSplitFactorSupported correct positive nodes condition
          hhead hdis
          (correct.pathDSeparated_of_dSeparated
            (successiveSplitOkFrom_dSeparated hok))
          assignment
      let innerSupported :=
        productSplitAllSupportedFrom correct positive
          (splitRest nodes head) condition
          (fun i hi =>
            hdis i
              (NodeSet.diff_subset_left nodes (NodeSet.singleton head) i hi))
          assignment (t :: rest)
          (members_splitRest_of_cons nodes hmem)
          (successiveSplitOkFrom_tail hok)
      let supportSucc :
          LocalDerivationSupport model assignment
            ((productSplitAllDerivation_succ (G := G) nodes condition hmem
                hdis
                (correct.pathDSeparated_of_dSeparated
                  (successiveSplitOkFrom_dSeparated hok))
                (productSplitAllDerivationFrom correct (splitRest nodes head)
                  condition
                  (fun i hi =>
                    hdis i
                      (NodeSet.diff_subset_left nodes (NodeSet.singleton head)
                        i hi))
                  (t :: rest) (members_splitRest_of_cons nodes hmem)
                  (successiveSplitOkFrom_tail hok))).compile correct) := by
        dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
          productSplitAllDerivation_succ]
        exact
          ⟨nodesSupported,
            ⟨fromSupported,
              ⟨unionSupported,
                ⟨fromSupported,
                  ⟨factorSupported,
                    ⟨kernelMultiplySupported,
                      ⟨fromSupported,
                        ⟨innerSupported,
                          ⟨headSupported, ⟨headSupported, ()⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
      have hder :
          productSplitAllDerivationFrom correct nodes condition hdis
            (head :: t :: rest) hmem hok =
            productSplitAllDerivation_succ (G := G) nodes condition hmem hdis
              (correct.pathDSeparated_of_dSeparated
                (successiveSplitOkFrom_dSeparated hok))
              (productSplitAllDerivationFrom correct (splitRest nodes head)
                condition
                (fun i hi =>
                  hdis i
                    (NodeSet.diff_subset_left nodes (NodeSet.singleton head)
                      i hi))
                (t :: rest) (members_splitRest_of_cons nodes hmem)
                (successiveSplitOkFrom_tail hok)) := by
        simp [productSplitAllDerivationFrom]
      hder ▸ supportSucc

noncomputable def productSplitAllSupported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    {model : FiniteLatentSCM S} (positive : ObservationallyPositive model)
    (nodes condition : NodeSet S)
    (hdis : NodeSet.Disjoint nodes condition)
    (hok : successiveSplitOk G nodes condition = true)
    (assignment : S.Assignment) :
    LocalDerivationSupport model assignment
      ((productSplitAllDerivation correct nodes condition hdis hok).compile
        correct) :=
  productSplitAllSupportedFrom correct positive nodes condition hdis
    assignment (NodeSet.members nodes) rfl
    (by simpa [successiveSplitOk] using hok)

/-- Exchange `do(X)` for an observation, then fully factor the
observational conditional along successive rest-versus-head
d-separations. -/
def productSplitAllIdentifiedIdDerivation {G : ObservedGraph S}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (separatedExchange :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (hok : successiveSplitOk G q.outcome q.action = true) :
    PathDoCalculusDerivation G q.sourceTerm
      (productSplitAllTerm q.outcome q.action) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (exchangeActionRule2Derivation q separatedExchange)
    (productSplitAllDerivation correct q.outcome q.action
      q.outcome_action_disjoint hok)

/--
Successive independent product-split of a composite outcome: after
rule 2 writes `P(Y | X)`, chain plus rule 1 factor every earliest
vertex from the remaining block once each rest-versus-head pair is
path-d-separated given `X` in `G`.  Every factor is an observational
conditional, so the formula is defined in every observationally
positive model.
-/
noncomputable def productSplitAllIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (obsPositive :
      forall {model : ExactModel S}, C.Mem model ->
        ObservationallyPositive model)
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (separatedExchange :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (hok : successiveSplitOk G q.outcome q.action = true) :
    PublishedJointCertificate C correct q where
  formula := productSplitAllTerm q.outcome q.action
  actionFree := productSplitAllTerm_actionFree q.outcome q.action
  derivation :=
    productSplitAllIdentifiedIdDerivation correct q separatedExchange hok
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      productSplitAllIdentifiedIdDerivation, exchangeActionRule2Derivation]
    let pyxSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome q.action assignment
    let formulaSupported :=
      productSplitAllTerm_supportedAt (obsPositive member) q.outcome
        q.action assignment
    let hleft := JointKernelQuery.sourceTerm_eq_rule2Left_empty_xw q
    let rule2LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    let hright :=
      JointKernelQuery.observationalCondition_eq_rule2Right_empty_xw q
    let rule2RightSupported :=
      ProbabilityTerm.SupportedAt.congr hright pyxSupported
    let exchangeSupported :
        LocalDerivationSupport model assignment
          ((exchangeActionRule2Derivation q separatedExchange).compile
            correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        exchangeActionRule2Derivation]
      exact
        ⟨sourceSupported,
          ⟨pyxSupported,
            ⟨rule2LeftSupported, ⟨rule2RightSupported, ()⟩⟩⟩⟩
    let allSupported :=
      productSplitAllSupported correct (obsPositive member) q.outcome
        q.action q.outcome_action_disjoint hok assignment
    exact
      ⟨sourceSupported,
        ⟨formulaSupported, ⟨exchangeSupported, allSupported⟩⟩⟩

/-- Boolean successive product-split: at least two outcome vertices,
underline d-separation of `Y` from `X`, and successive rest-versus-head
d-separation along `members`. -/
noncomputable def productSplitAllIdentifiedPublishedCertificate?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  match NodeSet.members q.outcome with
  | [] => none
  | [_] => none
  | _ :: _ :: _ =>
      if hex : G.dSeparated
          (GraphMutilation.barUnderline NodeSet.empty q.action)
          q.outcome q.action NodeSet.empty = true then
        if hok : successiveSplitOk G q.outcome q.action = true then
          some
            (productSplitAllIdentifiedPublishedCertificate
              (C := GraphModelClass.positive G)
              (fun {model}
                  (member : (GraphModelClass.positive G).Mem model) =>
                member.2)
              correct q
              (correct.pathDSeparated_of_dSeparated hex) hok)
        else
          none
      else
        none

theorem productSplitAllIdentifiedPublishedCertificate?_formula
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    {cert : PublishedJointCertificate (GraphModelClass.positive G) correct q}
    (h : productSplitAllIdentifiedPublishedCertificate? correct q = some cert) :
    cert.formula = productSplitAllTerm q.outcome q.action := by
  dsimp [productSplitAllIdentifiedPublishedCertificate?] at h
  split at h
  · cases h
  · cases h
  · split at h
    · split at h
      · next _hex _hok =>
          injection h with hcert
          subst hcert
          rfl
      · cases h
    · cases h

/-- The product-split formula's displayed value is strictly positive,
so it can be used as a Bayes denominator. -/
theorem productSplitAllCertificate_formula_num_pos
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    (cert : PublishedJointCertificate (GraphModelClass.positive G) correct q)
    (hform : cert.formula = productSplitAllTerm q.outcome q.action)
    (model : ExactModel S) (member : (GraphModelClass.positive G).Mem model)
    (assignment : S.Assignment) :
    0 <
      ((cert.supported model member assignment
          (q.supportedAt model assignment)).endpoints.2).1.num := by
  let denSup :=
    (cert.supported model member assignment
      (q.supportedAt model assignment)).endpoints.2
  let prodSup :=
    productSplitAllTerm_supportedAt member.2 q.outcome q.action assignment
  let prodSup' := ProbabilityTerm.SupportedAt.congr hform.symm prodSup
  cases ProbabilityResult.trans (ProbabilityResult.symm denSup.2) prodSup'.2 with
  | value hequiv =>
      have hprodPos :
          0 < prodSup'.1.num := by
        have hvals :
            ProbabilityResult.Equivalent (some prodSup'.1) (some prodSup.1) :=
          ProbabilityResult.trans (ProbabilityResult.symm prodSup'.2)
            (hform.symm ▸ prodSup.2)
        cases hvals with
        | value h =>
            exact
              (QProb.equiv_num_pos_iff h).mpr
                (productSplitAllTerm_num_pos member.2 q.outcome q.action
                  assignment)
      exact (QProb.equiv_num_pos_iff hequiv).mpr hprodPos

/-- Singleton 4.2: the unique free c-component is the singleton
outcome `{y}`.  The engine formula `∑_{S \ Y} Q[S]` reduces to an empty
complementary sum of the chain-rule kernel `P(Y | Pa_{V}(y))`. -/
theorem chainSingletonEngineTerm_eq
    (q : JointKernelQuery S) {y : Fin S.count}
    (hmem : NodeSet.members q.outcome = [y]) :
    ProbabilityTerm.marginalize
        (NodeSet.diff q.outcome q.outcome)
        (chainProduct NodeSet.full q.outcome) =
      ProbabilityTerm.marginalize NodeSet.empty
        (.kernel ⟨NodeSet.union q.outcome NodeSet.empty,
          NodeSet.empty, chainCondition NodeSet.full y⟩) := by
  have hy : q.outcome = NodeSet.singleton y :=
    NodeSet.eq_singleton_of_members hmem
  have hcp :
      chainProduct NodeSet.full q.outcome =
        .kernel (chainKernel NodeSet.full y) :=
    chainProduct_of_members_singleton _ hmem
  have hck :
      ProbabilityTerm.kernel (chainKernel NodeSet.full y) =
        .kernel ⟨q.outcome, NodeSet.empty,
          chainCondition NodeSet.full y⟩ := by
    simp [chainKernel, hy]
  have hdiff : NodeSet.diff q.outcome q.outcome = NodeSet.empty :=
    NodeSet.diff_self _
  have hunion :
      NodeSet.union q.outcome NodeSet.empty = q.outcome :=
    NodeSet.union_empty_right _
  calc
    ProbabilityTerm.marginalize
        (NodeSet.diff q.outcome q.outcome)
        (chainProduct NodeSet.full q.outcome) =
      ProbabilityTerm.marginalize NodeSet.empty
        (.kernel (chainKernel NodeSet.full y)) := by
      rw [hdiff, hcp]
    _ = ProbabilityTerm.marginalize NodeSet.empty
          (.kernel ⟨q.outcome, NodeSet.empty,
            chainCondition NodeSet.full y⟩) := by
      rw [hck]
    _ = ProbabilityTerm.marginalize NodeSet.empty
          (.kernel ⟨NodeSet.union q.outcome NodeSet.empty,
            NodeSet.empty, chainCondition NodeSet.full y⟩) := by
      rw [hunion]

theorem chainSingleton_disjoint_predecessors
    (q : JointKernelQuery S) {y : Fin S.count}
    (hmem : NodeSet.members q.outcome = [y]) :
    NodeSet.Disjoint q.outcome (chainCondition NodeSet.full y) :=
  (NodeSet.eq_singleton_of_members hmem) ▸
    disjoint_singleton_chainCondition NodeSet.full y

/-- Rule 1 with empty original action: the side-condition graph is
ordinary `G` (no incoming cut) and the given set is `W`. -/
theorem pathDSeparated_rule1_empty_action
    (G : ObservedGraph S) (y z w : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) y z w) :
    PathSpecification.PathDSeparated G
      (GraphMutilation.bar NodeSet.empty) y z
      (NodeSet.union NodeSet.empty w) := by
  simpa [NodeSet.union_empty_left] using separated

theorem insertCondition_rule1Right_eq
    (q : JointKernelQuery S) (target : NodeSet S) :
    ProbabilityTerm.kernel ⟨q.outcome, NodeSet.empty, q.action⟩ =
      .kernel
        (rule1Right NodeSet.empty q.outcome
          (NodeSet.diff target q.action) q.action) := by
  simp [rule1Right]

theorem insertCondition_rule1Left_eq
    (q : JointKernelQuery S) {target : NodeSet S}
    (hsubset : NodeSet.Subset q.action target) :
    ProbabilityTerm.kernel ⟨q.outcome, NodeSet.empty, target⟩ =
      .kernel
        (rule1Left NodeSet.empty q.outcome
          (NodeSet.diff target q.action) q.action) := by
  simp [rule1Left]
  rw [NodeSet.diff_union_eq hsubset]

theorem chainSingleton_rule1Right_eq
    (q : JointKernelQuery S) (y : Fin S.count) :
    ProbabilityTerm.kernel ⟨q.outcome, NodeSet.empty, q.action⟩ =
      .kernel
        (rule1Right NodeSet.empty q.outcome
          (extraPredecessors NodeSet.full y q.action) q.action) :=
  insertCondition_rule1Right_eq q (chainCondition NodeSet.full y)

theorem chainSingleton_rule1Left_eq
    (q : JointKernelQuery S) {y : Fin S.count}
    (hsubset :
      NodeSet.Subset q.action (chainCondition NodeSet.full y)) :
    ProbabilityTerm.kernel
        ⟨q.outcome, NodeSet.empty, chainCondition NodeSet.full y⟩ =
      .kernel
        (rule1Left NodeSet.empty q.outcome
          (extraPredecessors NodeSet.full y q.action) q.action) :=
  insertCondition_rule1Left_eq q hsubset

/--
Rule 1 inserts extra conditioners `target \ X` into `P(Y | X)`, recovering
`P(Y | target)` once `Y ⊥ (target \ X) | X` in `G` and `X ⊆ target`.
-/
def insertConditionRule1Derivation {G : ObservedGraph S}
    (q : JointKernelQuery S) (target : NodeSet S)
    (hsubset : NodeSet.Subset q.action target)
    (disjointYT : NodeSet.Disjoint q.outcome target)
    (separatedInsert :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) q.outcome
        (NodeSet.diff target q.action) q.action) :
    PathDoCalculusDerivation G
      (.kernel ⟨q.outcome, NodeSet.empty, q.action⟩)
      (.kernel ⟨q.outcome, NodeSet.empty, target⟩) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (insertCondition_rule1Right_eq q target)
    (insertCondition_rule1Left_eq q hsubset)
    (DoCalculusDerivation.symm
      (G := G) (separation := pathRuleSeparation G)
      (DoCalculusDerivation.doRule
        (G := G) (separation := pathRuleSeparation G)
        (DoRuleApplication.rule1 (G := G) (separation := pathRuleSeparation G)
          NodeSet.empty q.outcome (NodeSet.diff target q.action) q.action
          (FourWayDisjoint.emptyAction q.outcome
            (NodeSet.diff target q.action) q.action
            (NodeSet.disjoint_of_subset_right disjointYT
              (NodeSet.diff_subset_left _ _))
            q.outcome_action_disjoint
            (NodeSet.disjoint_diff_right _ _))
          (pathDSeparated_rule1_empty_action G q.outcome
            (NodeSet.diff target q.action) q.action
            separatedInsert))))

/--
Rule 1 inserts extra topological predecessors `Pa_V(y) \ X` into the
observational conditional `P(Y | X)`, recovering the chain-rule kernel
`P(Y | Pa_V(y))` once `Y ⊥ (Pa_V(y) \ X) | X` in `G`.
-/
def insertPredecessorsRule1Derivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {y : Fin S.count}
    (hmem : NodeSet.members q.outcome = [y])
    (hsubset :
      NodeSet.Subset q.action (chainCondition NodeSet.full y))
    (separatedInsert :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) q.outcome
        (extraPredecessors NodeSet.full y q.action) q.action) :
    PathDoCalculusDerivation G
      (.kernel ⟨q.outcome, NodeSet.empty, q.action⟩)
      (.kernel ⟨q.outcome, NodeSet.empty,
        chainCondition NodeSet.full y⟩) :=
  insertConditionRule1Derivation q (chainCondition NodeSet.full y) hsubset
    (chainSingleton_disjoint_predecessors q hmem) separatedInsert

/-- Rule 2 exchange of the action, rule 1 insertion of extra
predecessors, then an empty complementary sum so the formula is the
singleton-4.2 engine output. -/
def chainSingletonIdentifiedIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {y : Fin S.count}
    (hmem : NodeSet.members q.outcome = [y])
    (hsubset :
      NodeSet.Subset q.action (chainCondition NodeSet.full y))
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (separatedInsert :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) q.outcome
        (extraPredecessors NodeSet.full y q.action) q.action) :
    PathDoCalculusDerivation G q.sourceTerm
      (.marginalize (NodeSet.diff q.outcome q.outcome)
        (chainProduct NodeSet.full q.outcome)) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (exchangeActionRule2Derivation q separated)
    (DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G)
      (insertPredecessorsRule1Derivation q hmem hsubset separatedInsert)
      (DoCalculusDerivation.eqCongr
        (G := G) (separation := pathRuleSeparation G)
        rfl
        (chainSingletonEngineTerm_eq q hmem)
        (DoCalculusDerivation.marginalization
          (G := G) (separation := pathRuleSeparation G)
          NodeSet.empty q.outcome NodeSet.empty
          (chainCondition NodeSet.full y)
          (FourWayDisjoint.emptyActionEmptyZ q.outcome
            (chainCondition NodeSet.full y)
            (chainSingleton_disjoint_predecessors q hmem)))))

/-- Positive-class singleton 4.2 certificate: formula matches
`Legacy.identifyJoint` on a one-vertex free c-component equal to `Y`.  The
action may be a subset of the topological predecessors; extra
predecessors are inserted by rule 1. -/
noncomputable def chainSingletonIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (obsPositive :
      forall {model : ExactModel S}, C.Mem model ->
        ObservationallyPositive model)
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    {y : Fin S.count}
    (hmem : NodeSet.members q.outcome = [y])
    (hsubset :
      NodeSet.Subset q.action (chainCondition NodeSet.full y))
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (separatedInsert :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) q.outcome
        (extraPredecessors NodeSet.full y q.action) q.action) :
    PublishedJointCertificate C correct q where
  formula :=
    .marginalize (NodeSet.diff q.outcome q.outcome)
      (chainProduct NodeSet.full q.outcome)
  actionFree := by
    change (chainProduct NodeSet.full q.outcome).ActionFree
    exact chainProduct_actionFree NodeSet.full q.outcome
  derivation :=
    chainSingletonIdentifiedIdDerivation q hmem hsubset separated
      separatedInsert
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      chainSingletonIdentifiedIdDerivation, exchangeActionRule2Derivation,
      insertPredecessorsRule1Derivation]
    let pyxSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome q.action assignment
    let predSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome (chainCondition NodeSet.full y) assignment
    let formulaKernelMarginalSupported :=
      observationalConditionalMarginal_supportedAt model
        (obsPositive member) q.outcome (chainCondition NodeSet.full y)
        (NodeSet.diff q.outcome q.outcome) assignment
    have hchain :
        chainProduct NodeSet.full q.outcome =
          .kernel ⟨q.outcome, NodeSet.empty,
            chainCondition NodeSet.full y⟩ := by
      have hcp := chainProduct_of_members_singleton
        (remaining := NodeSet.full) hmem
      have hy : q.outcome = NodeSet.singleton y :=
        NodeSet.eq_singleton_of_members hmem
      rw [hcp]
      simp only [chainKernel]
      rw [← hy]
    let formulaSupported :=
      ProbabilityTerm.SupportedAt.congr
        (congrArg
          (ProbabilityTerm.marginalize (NodeSet.diff q.outcome q.outcome))
          hchain.symm)
        formulaKernelMarginalSupported
    let hleft := JointKernelQuery.sourceTerm_eq_rule2Left_empty_xw q
    let rule2LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    let hright :=
      JointKernelQuery.observationalCondition_eq_rule2Right_empty_xw q
    let rule2RightSupported :=
      ProbabilityTerm.SupportedAt.congr hright pyxSupported
    let exchangeSupported :
        LocalDerivationSupport model assignment
          ((exchangeActionRule2Derivation q separated).compile correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        exchangeActionRule2Derivation]
      exact
        ⟨sourceSupported,
          ⟨pyxSupported,
            ⟨rule2LeftSupported, ⟨rule2RightSupported, ()⟩⟩⟩⟩
    let hrule1Right := chainSingleton_rule1Right_eq q y
    let hrule1Left := chainSingleton_rule1Left_eq q hsubset
    let rule1RightSupported :=
      ProbabilityTerm.SupportedAt.congr hrule1Right pyxSupported
    let rule1LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hrule1Left predSupported
    let insertSupported :
        LocalDerivationSupport model assignment
          ((insertPredecessorsRule1Derivation q hmem hsubset
            separatedInsert).compile correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        insertPredecessorsRule1Derivation]
      exact
        ⟨pyxSupported,
          ⟨predSupported,
            ⟨rule1RightSupported,
              ⟨rule1LeftSupported,
                ⟨rule1LeftSupported, ⟨rule1RightSupported, ()⟩⟩⟩⟩⟩⟩
    let hengine := chainSingletonEngineTerm_eq q hmem
    let innerRightSupported :=
      ProbabilityTerm.SupportedAt.congr hengine formulaSupported
    let margSupported :
        LocalDerivationSupport model assignment
          ((DoCalculusDerivation.eqCongr
              (G := G) (separation := pathRuleSeparation G)
              rfl (chainSingletonEngineTerm_eq q hmem)
              (DoCalculusDerivation.marginalization
                (G := G) (separation := pathRuleSeparation G)
                NodeSet.empty q.outcome NodeSet.empty
                (chainCondition NodeSet.full y)
                (FourWayDisjoint.emptyActionEmptyZ q.outcome
                  (chainCondition NodeSet.full y)
                  (chainSingleton_disjoint_predecessors q hmem)))).mapRules
            (PathDoRuleApplication.compile correct)) :=
      ⟨predSupported,
        ⟨formulaSupported,
          ⟨predSupported, ⟨innerRightSupported, ()⟩⟩⟩⟩
    exact
      ⟨sourceSupported,
        ⟨formulaSupported,
          ⟨exchangeSupported,
            ⟨pyxSupported,
              ⟨formulaSupported,
                ⟨insertSupported, margSupported⟩⟩⟩⟩⟩⟩

/-- Boolean singleton-outcome, predecessor-subset, underline
d-separation, and observational d-separation of extra predecessors
unpack to the engine-matching 4.2 certificate.  Empty extra
predecessors are vacuously d-separated. -/
noncomputable def chainSingletonIdentifiedPublishedCertificate?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  match hmem : NodeSet.members q.outcome with
  | [y] =>
      if hsub :
          NodeSet.subsetBool q.action
            (chainCondition NodeSet.full y) = true then
        if h : G.dSeparated
            (GraphMutilation.barUnderline NodeSet.empty q.action)
            q.outcome q.action NodeSet.empty = true then
          let extra := extraPredecessors NodeSet.full y q.action
          let hsubset :=
            (NodeSet.subsetBool_eq_true_iff q.action
              (chainCondition NodeSet.full y)).mp hsub
          if hW : NodeSet.isEmpty extra = true then
            some
              (chainSingletonIdentifiedPublishedCertificate
                (C := GraphModelClass.positive G)
                (fun {model}
                    (member : (GraphModelClass.positive G).Mem model) =>
                  member.2)
                correct q hmem hsubset
                (correct.pathDSeparated_of_dSeparated h)
                (PathSpecification.PathDSeparated.of_isEmpty_right G
                  (GraphMutilation.bar NodeSet.empty) q.outcome extra
                  q.action hW))
          else if hins : G.dSeparated
              (GraphMutilation.bar NodeSet.empty) q.outcome extra
              q.action = true then
            some
              (chainSingletonIdentifiedPublishedCertificate
                (C := GraphModelClass.positive G)
                (fun {model}
                    (member : (GraphModelClass.positive G).Mem model) =>
                  member.2)
                correct q hmem hsubset
                (correct.pathDSeparated_of_dSeparated h)
                (correct.pathDSeparated_of_dSeparated hins))
          else
            none
        else
          none
      else
        none
  | _ => none

/-- Consecutive two-vertex chain-rule term
`∑_i P(y | pred(y)) P(i | pred(i))`.  The later vertex is on the left,
matching both `chainProduct` in the engine and the order produced by
`DoCalculusDerivation.chain`; no syntactic commutativity rule is assumed. -/
def twoVertexChainTerm {S : ObservedSignature} (j : Fin S.count)
    (hpos : 0 < j.val) : ProbabilityTerm S :=
  .marginalize (NodeSet.singleton (predIndex j hpos))
    (.multiply
      (.kernel (chainKernel NodeSet.full j))
      (.kernel (chainKernel NodeSet.full (predIndex j hpos))))

theorem twoVertexChainTerm_actionFree {S : ObservedSignature}
    (j : Fin S.count) (hpos : 0 < j.val) :
    (twoVertexChainTerm j hpos).ActionFree :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- The two-vertex formula is the general consecutive chain at step 1. -/
theorem twoVertexChainTerm_eq_consecutive {S : ObservedSignature}
    (j : Fin S.count) (hpos : 0 < j.val) :
    twoVertexChainTerm j hpos =
      consecutiveChainTerm j 1 (Nat.succ_le_of_lt hpos) := by
  have h : 1 ≤ j.val := Nat.succ_le_of_lt hpos
  have hi : predIndex j hpos = predIndex j (Nat.lt_of_succ_le h) :=
    Fin.eq_of_val_eq (by simp [predIndex])
  rw [consecutiveChainTerm_one]
  simp [twoVertexChainTerm, hi]

theorem twoVertex_disjoint_predecessors
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (hpos : 0 < j.val) :
    NodeSet.Disjoint q.outcome
      (chainCondition NodeSet.full (predIndex j hpos)) :=
  (NodeSet.eq_singleton_of_members hmem) ▸
    disjoint_later_chainCondition NodeSet.full (predIndex_lt j hpos)

def twoVertexFourWay {S : ObservedSignature} (j : Fin S.count)
    (hpos : 0 < j.val) :
    FourWayDisjoint NodeSet.empty (NodeSet.singleton j)
      (NodeSet.singleton (predIndex j hpos))
      (chainCondition NodeSet.full (predIndex j hpos)) :=
  FourWayDisjoint.emptyAction _ _ _
    (NodeSet.disjoint_singletons_of_ne (Ne.symm (predIndex_ne j hpos)))
    (disjoint_later_chainCondition NodeSet.full (predIndex_lt j hpos))
    (disjoint_singleton_chainCondition NodeSet.full (predIndex j hpos))

theorem twoVertex_chainRight_eq {S : ObservedSignature}
    (j : Fin S.count) (hpos : 0 < j.val) :
    ProbabilityTerm.multiply
        (.kernel (chainKernel NodeSet.full j))
        (.kernel (chainKernel NodeSet.full (predIndex j hpos))) =
      .multiply
        (.kernel ⟨NodeSet.singleton j, NodeSet.empty,
          NodeSet.union (NodeSet.singleton (predIndex j hpos))
            (chainCondition NodeSet.full (predIndex j hpos))⟩)
        (.kernel ⟨NodeSet.singleton (predIndex j hpos), NodeSet.empty,
          chainCondition NodeSet.full (predIndex j hpos)⟩) := by
  simp only [chainKernel]
  rw [chainCondition_predIndex j hpos]

theorem twoVertex_fromPred_right_eq {S : ObservedSignature}
    (j : Fin S.count) (hpos : 0 < j.val) :
    twoVertexChainTerm j hpos =
      ProbabilityTerm.marginalize (NodeSet.singleton (predIndex j hpos))
        (.multiply
          (.kernel ⟨NodeSet.singleton j, NodeSet.empty,
            NodeSet.union (NodeSet.singleton (predIndex j hpos))
              (chainCondition NodeSet.full (predIndex j hpos))⟩)
          (.kernel ⟨NodeSet.singleton (predIndex j hpos), NodeSet.empty,
            chainCondition NodeSet.full (predIndex j hpos)⟩)) := by
  simp [twoVertexChainTerm, twoVertex_chainRight_eq]

/-- From `P(Y | Pa_V(i))` to the consecutive two-vertex chain term,
by empty-action marginalization of the `{i, y}` joint and the chain
rule. -/
def twoVertexFromPredDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (hpos : 0 < j.val) :
    PathDoCalculusDerivation G
      (.kernel ⟨q.outcome, NodeSet.empty,
        chainCondition NodeSet.full (predIndex j hpos)⟩)
      (twoVertexChainTerm j hpos) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (by rw [NodeSet.eq_singleton_of_members hmem])
    (twoVertex_fromPred_right_eq j hpos)
    (DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G)
      (DoCalculusDerivation.marginalization
        (G := G) (separation := pathRuleSeparation G)
        NodeSet.empty (NodeSet.singleton j)
        (NodeSet.singleton (predIndex j hpos))
        (chainCondition NodeSet.full (predIndex j hpos))
        (twoVertexFourWay j hpos))
      (DoCalculusDerivation.marginalizeCongr
        (G := G) (separation := pathRuleSeparation G)
        (NodeSet.singleton (predIndex j hpos))
        (DoCalculusDerivation.chain
          (G := G) (separation := pathRuleSeparation G)
          NodeSet.empty (NodeSet.singleton j)
          (NodeSet.singleton (predIndex j hpos))
          (chainCondition NodeSet.full (predIndex j hpos))
          (twoVertexFourWay j hpos))))

/-- Rule 2 exchange, rule 1 insert to `Pa_V(i)`, then the consecutive
two-vertex chain factorization. -/
def twoVertexIdentifiedIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (hpos : 0 < j.val)
    (hsubset :
      NodeSet.Subset q.action
        (chainCondition NodeSet.full (predIndex j hpos)))
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (separatedInsert :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) q.outcome
        (extraPredecessors NodeSet.full (predIndex j hpos) q.action)
        q.action) :
    PathDoCalculusDerivation G q.sourceTerm (twoVertexChainTerm j hpos) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (exchangeActionRule2Derivation q separated)
    (DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G)
      (insertConditionRule1Derivation q
        (chainCondition NodeSet.full (predIndex j hpos)) hsubset
        (twoVertex_disjoint_predecessors q hmem hpos) separatedInsert)
      (twoVertexFromPredDerivation q hmem hpos))

/-- Positive-class consecutive two-vertex 4.2: `Y = {y}` with
immediate predecessor `i`, action contained in `Pa_V(i)`. -/
noncomputable def twoVertexIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (obsPositive :
      forall {model : ExactModel S}, C.Mem model ->
        ObservationallyPositive model)
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (hpos : 0 < j.val)
    (hsubset :
      NodeSet.Subset q.action
        (chainCondition NodeSet.full (predIndex j hpos)))
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (separatedInsert :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) q.outcome
        (extraPredecessors NodeSet.full (predIndex j hpos) q.action)
        q.action) :
    PublishedJointCertificate C correct q where
  formula := twoVertexChainTerm j hpos
  actionFree := twoVertexChainTerm_actionFree j hpos
  derivation :=
    twoVertexIdentifiedIdDerivation q hmem hpos hsubset separated
      separatedInsert
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      twoVertexIdentifiedIdDerivation]
    let i := predIndex j hpos
    let pred := chainCondition NodeSet.full i
    let pyxSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome q.action assignment
    let predSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome pred assignment
    let formulaSupported :=
      observationalConditionalMarginal_supportedAt model
        (obsPositive member) q.outcome pred (NodeSet.singleton i)
        assignment
    -- The formula is a marg of a product, not of the joint kernel.
    -- Transport along the chain-rule denotation at every variant below.
    let hleft := JointKernelQuery.sourceTerm_eq_rule2Left_empty_xw q
    let rule2LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    let hright :=
      JointKernelQuery.observationalCondition_eq_rule2Right_empty_xw q
    let rule2RightSupported :=
      ProbabilityTerm.SupportedAt.congr hright pyxSupported
    let exchangeSupported :
        LocalDerivationSupport model assignment
          ((exchangeActionRule2Derivation q separated).compile correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        exchangeActionRule2Derivation]
      exact
        ⟨sourceSupported,
          ⟨pyxSupported,
            ⟨rule2LeftSupported, ⟨rule2RightSupported, ()⟩⟩⟩⟩
    let hrule1Right := insertCondition_rule1Right_eq q pred
    let hrule1Left := insertCondition_rule1Left_eq q hsubset
    let rule1RightSupported :=
      ProbabilityTerm.SupportedAt.congr hrule1Right pyxSupported
    let rule1LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hrule1Left predSupported
    let insertSupported :
        LocalDerivationSupport model assignment
          ((insertConditionRule1Derivation q pred hsubset
            (twoVertex_disjoint_predecessors q hmem hpos)
            separatedInsert).compile correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        insertConditionRule1Derivation]
      exact
        ⟨pyxSupported,
          ⟨predSupported,
            ⟨rule1RightSupported,
              ⟨rule1LeftSupported,
                ⟨rule1LeftSupported, ⟨rule1RightSupported, ()⟩⟩⟩⟩⟩⟩
    let hy : q.outcome = NodeSet.singleton j :=
      NodeSet.eq_singleton_of_members hmem
    let predSingletonSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        (NodeSet.singleton j) pred assignment
    let predSingletonSupported' :=
      ProbabilityTerm.SupportedAt.congr (by rw [hy]) predSupported
    let formulaProductSupported :=
      observationalConditionalMarginal_supportedAt model
        (obsPositive member) (NodeSet.singleton j) pred
        (NodeSet.singleton i) assignment
    -- Replace with product-marginal support after chain at each variant.
    let jointKernelSupported (variant : S.Assignment) :=
      observationalConditional_supportedAt model (obsPositive member)
        (NodeSet.union (NodeSet.singleton j) (NodeSet.singleton i))
        pred variant
    let kjSupported (variant : S.Assignment) :=
      observationalConditional_supportedAt model (obsPositive member)
        (NodeSet.singleton j)
        (NodeSet.union (NodeSet.singleton i) pred) variant
    let kiSupported (variant : S.Assignment) :=
      observationalConditional_supportedAt model (obsPositive member)
        (NodeSet.singleton i) pred variant
    let productSupported (variant : S.Assignment) :=
      ProbabilityTerm.multiply_supportedAt
        (kjSupported variant) (kiSupported variant)
    let hprod := twoVertex_chainRight_eq j hpos
    let formulaTrueSupported :=
      observationalConditionalMarginal_supportedAt model
        (obsPositive member) (NodeSet.singleton j)
        (NodeSet.union (NodeSet.singleton i) pred)
        (NodeSet.singleton i) assignment
    -- formula is marg of multiply kj ki; support via sum of products.
    let formulaSupported' :
        (twoVertexChainTerm j hpos).SupportedAt model assignment := by
      simpa [twoVertexChainTerm, ProbabilityTerm.denote,
        twoVertex_chainRight_eq j hpos] using
        ProbabilityResult.sum_map_supported
          (ProbabilityTerm.marginalAssignments S (NodeSet.singleton i)
            assignment)
          (fun variant =>
            (ProbabilityTerm.multiply
              (.kernel ⟨NodeSet.singleton j, NodeSet.empty,
                NodeSet.union (NodeSet.singleton i) pred⟩)
              (.kernel ⟨NodeSet.singleton i, NodeSet.empty, pred⟩)).denote
              model variant)
          (fun variant => productSupported variant)
    let jointMargSupported := by
      simpa [ProbabilityTerm.denote] using
        ProbabilityResult.sum_map_supported
          (ProbabilityTerm.marginalAssignments S (NodeSet.singleton i)
            assignment)
          (fun variant =>
            (ProbabilityTerm.kernel
              ⟨NodeSet.union (NodeSet.singleton j) (NodeSet.singleton i),
                NodeSet.empty, pred⟩).denote model variant)
          (fun variant => jointKernelSupported variant)
    let innerRightSupported :=
      ProbabilityTerm.SupportedAt.congr
        (twoVertex_fromPred_right_eq j hpos) formulaSupported'
    let fromPredSupported :
        LocalDerivationSupport model assignment
          ((twoVertexFromPredDerivation q hmem hpos).compile correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        twoVertexFromPredDerivation]
      exact
        ⟨predSupported,
          ⟨formulaSupported',
            ⟨predSingletonSupported',
              ⟨innerRightSupported,
                ⟨⟨predSingletonSupported', ⟨jointMargSupported, ()⟩⟩,
                  ⟨jointMargSupported,
                    ⟨innerRightSupported,
                      fun variant _hv =>
                        ⟨jointKernelSupported variant,
                          ⟨productSupported variant, ()⟩⟩⟩⟩⟩⟩⟩⟩⟩
    exact
      ⟨sourceSupported,
        ⟨formulaSupported',
          ⟨exchangeSupported,
            ⟨pyxSupported,
              ⟨formulaSupported',
                ⟨insertSupported, fromPredSupported⟩⟩⟩⟩⟩⟩

/-- Boolean consecutive two-vertex 4.2 unpacks on the positive class. -/
noncomputable def twoVertexIdentifiedPublishedCertificate?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  match hmem : NodeSet.members q.outcome with
  | [j] =>
      if hpos : 0 < j.val then
        if hsub :
            NodeSet.subsetBool q.action
              (chainCondition NodeSet.full (predIndex j hpos)) = true then
          if h : G.dSeparated
              (GraphMutilation.barUnderline NodeSet.empty q.action)
              q.outcome q.action NodeSet.empty = true then
            let extra :=
              extraPredecessors NodeSet.full (predIndex j hpos) q.action
            let hsubset :=
              (NodeSet.subsetBool_eq_true_iff q.action
                (chainCondition NodeSet.full (predIndex j hpos))).mp hsub
            if hW : NodeSet.isEmpty extra = true then
              some
                (twoVertexIdentifiedPublishedCertificate
                  (C := GraphModelClass.positive G)
                  (fun {model}
                      (member : (GraphModelClass.positive G).Mem model) =>
                    member.2)
                  correct q hmem hpos hsubset
                  (correct.pathDSeparated_of_dSeparated h)
                  (PathSpecification.PathDSeparated.of_isEmpty_right G
                    (GraphMutilation.bar NodeSet.empty) q.outcome extra
                    q.action hW))
            else if hins : G.dSeparated
                (GraphMutilation.bar NodeSet.empty) q.outcome extra
                q.action = true then
              some
                (twoVertexIdentifiedPublishedCertificate
                  (C := GraphModelClass.positive G)
                  (fun {model}
                      (member : (GraphModelClass.positive G).Mem model) =>
                    member.2)
                  correct q hmem hpos hsubset
                  (correct.pathDSeparated_of_dSeparated h)
                  (correct.pathDSeparated_of_dSeparated hins))
            else
              none
          else
            none
        else
          none
      else
        none
  | _ => none

/-- Three consecutive chain-rule factors, summed off the two earlier
vertices: `∑_{i,k} P(k | Pa(k)) P(i | k, Pa(k)) P(y | i, k, Pa(k))`. -/
def threeVertexChainTerm {S : ObservedSignature} (j : Fin S.count)
    (h1 : 1 < j.val) : ProbabilityTerm S :=
  let hpos : 0 < j.val := Nat.lt_trans Nat.zero_lt_one h1
  let i := predIndex j hpos
  let k := predIndex2 j h1
  .marginalize (NodeSet.union (NodeSet.singleton i) (NodeSet.singleton k))
    (.multiply
      (.kernel (chainKernel NodeSet.full j))
      (.multiply
        (.kernel (chainKernel NodeSet.full i))
        (.kernel (chainKernel NodeSet.full k))))

theorem threeVertexChainTerm_actionFree {S : ObservedSignature}
    (j : Fin S.count) (h1 : 1 < j.val) :
    (threeVertexChainTerm j h1).ActionFree :=
  ⟨fun _ => rfl, ⟨fun _ => rfl, fun _ => rfl⟩⟩

/-- The three-vertex formula is the general consecutive chain at step 2. -/
theorem threeVertexChainTerm_eq_consecutive {S : ObservedSignature}
    (j : Fin S.count) (h1 : 1 < j.val) :
    threeVertexChainTerm j h1 =
      consecutiveChainTerm j 2 (Nat.succ_le_of_lt h1) := by
  have h : 2 ≤ j.val := Nat.succ_le_of_lt h1
  have hpos : 0 < j.val := Nat.lt_trans Nat.zero_lt_one h1
  have hi : predIndex j hpos =
      predIndex j (Nat.lt_of_succ_le (Nat.le_trans (Nat.le_succ 1) h)) :=
    Fin.eq_of_val_eq (by simp [predIndex])
  have hk : predIndex2 j h1 = predIndex2 j (Nat.lt_of_succ_le h) :=
    Fin.eq_of_val_eq (by simp [predIndex2, predIndex])
  rw [consecutiveChainTerm_two]
  simp [threeVertexChainTerm, hi, hk]

theorem threeVertex_disjoint_predecessors
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (h1 : 1 < j.val) :
    NodeSet.Disjoint q.outcome
      (chainCondition NodeSet.full (predIndex2 j h1)) :=
  (NodeSet.eq_singleton_of_members hmem) ▸
    disjoint_later_chainCondition NodeSet.full
      (Nat.lt_trans (predIndex2_lt j h1)
        (predIndex_lt j (Nat.lt_trans Nat.zero_lt_one h1)))

def threeVertexSummed {S : ObservedSignature} (j : Fin S.count)
    (h1 : 1 < j.val) : NodeSet S :=
  let hpos : 0 < j.val := Nat.lt_trans Nat.zero_lt_one h1
  NodeSet.union (NodeSet.singleton (predIndex j hpos))
    (NodeSet.singleton (predIndex2 j h1))

theorem threeVertex_pa_eq {S : ObservedSignature}
    (j : Fin S.count) (h1 : 1 < j.val) :
    chainCondition NodeSet.full j =
      NodeSet.union (threeVertexSummed j h1)
        (chainCondition NodeSet.full (predIndex2 j h1)) := by
  have h := chainCondition_predIndex2 j h1
  simp only [threeVertexSummed]
  exact h.trans (NodeSet.union_assoc _ _ _).symm

def threeVertexFourWayOuter {S : ObservedSignature} (j : Fin S.count)
    (h1 : 1 < j.val) :
    FourWayDisjoint NodeSet.empty (NodeSet.singleton j)
      (threeVertexSummed j h1)
      (chainCondition NodeSet.full (predIndex2 j h1)) :=
  let hpos : 0 < j.val := Nat.lt_trans Nat.zero_lt_one h1
  FourWayDisjoint.emptyAction _ _ _
    (NodeSet.disjoint_union_of
      (NodeSet.disjoint_singletons_of_ne (Ne.symm (predIndex_ne j hpos)))
      (NodeSet.disjoint_singletons_of_ne (by
        intro heq
        have hlt : (predIndex2 j h1).val < j.val :=
          Nat.lt_trans (predIndex2_lt j h1) (predIndex_lt j hpos)
        have hval : (predIndex2 j h1).val = j.val :=
          congrArg Fin.val heq.symm
        exact Nat.lt_irrefl _ (hval ▸ hlt))))
    (disjoint_later_chainCondition NodeSet.full
      (Nat.lt_trans (predIndex2_lt j h1) (predIndex_lt j hpos)))
    (NodeSet.disjoint_union_left_of
      (disjoint_later_chainCondition NodeSet.full (predIndex2_lt j h1))
      (disjoint_singleton_chainCondition NodeSet.full (predIndex2 j h1)))

def threeVertexFourWayInner {S : ObservedSignature} (j : Fin S.count)
    (h1 : 1 < j.val) :
    FourWayDisjoint NodeSet.empty
      (NodeSet.singleton (predIndex j (Nat.lt_trans Nat.zero_lt_one h1)))
      (NodeSet.singleton (predIndex2 j h1))
      (chainCondition NodeSet.full (predIndex2 j h1)) :=
  let hpos : 0 < j.val := Nat.lt_trans Nat.zero_lt_one h1
  FourWayDisjoint.emptyAction _ _ _
    (NodeSet.disjoint_singletons_of_ne
      (Ne.symm (predIndex_ne (predIndex j hpos)
        (predIndex_pos_of_two j h1))))
    (disjoint_later_chainCondition NodeSet.full (predIndex2_lt j h1))
    (disjoint_singleton_chainCondition NodeSet.full (predIndex2 j h1))

theorem threeVertex_fromPred_left_eq
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (h1 : 1 < j.val) :
    ProbabilityTerm.kernel
        ⟨q.outcome, NodeSet.empty,
          chainCondition NodeSet.full (predIndex2 j h1)⟩ =
      .kernel ⟨NodeSet.singleton j, NodeSet.empty,
        chainCondition NodeSet.full (predIndex2 j h1)⟩ := by
  rw [NodeSet.eq_singleton_of_members hmem]

theorem threeVertex_summed_eq {S : ObservedSignature}
    (j : Fin S.count) (h1 : 1 < j.val) :
    threeVertexSummed j h1 =
      NodeSet.union
        (NodeSet.singleton (predIndex j (Nat.lt_trans Nat.zero_lt_one h1)))
        (NodeSet.singleton (predIndex2 j h1)) :=
  rfl

/-- `eqCongr` left of the inner `{i, k}` chain: the summed mask is
those two singletons. -/
theorem threeVertex_innerChainLeft_eq {S : ObservedSignature}
    (j : Fin S.count) (h1 : 1 < j.val) :
    ProbabilityTerm.kernel
        ⟨threeVertexSummed j h1, NodeSet.empty,
          chainCondition NodeSet.full (predIndex2 j h1)⟩ =
      .kernel ⟨
        NodeSet.union
          (NodeSet.singleton (predIndex j (Nat.lt_trans Nat.zero_lt_one h1)))
          (NodeSet.singleton (predIndex2 j h1)),
        NodeSet.empty,
        chainCondition NodeSet.full (predIndex2 j h1)⟩ := by
  rw [threeVertex_summed_eq]

theorem threeVertex_innerProduct_eq {S : ObservedSignature}
    (j : Fin S.count) (h1 : 1 < j.val) :
    ProbabilityTerm.multiply
        (.kernel (chainKernel NodeSet.full
          (predIndex j (Nat.lt_trans Nat.zero_lt_one h1))))
        (.kernel (chainKernel NodeSet.full (predIndex2 j h1))) =
      .multiply
        (.kernel ⟨NodeSet.singleton
            (predIndex j (Nat.lt_trans Nat.zero_lt_one h1)),
          NodeSet.empty,
          NodeSet.union (NodeSet.singleton (predIndex2 j h1))
            (chainCondition NodeSet.full (predIndex2 j h1))⟩)
        (.kernel ⟨NodeSet.singleton (predIndex2 j h1), NodeSet.empty,
          chainCondition NodeSet.full (predIndex2 j h1)⟩) := by
  have hpos : 0 < j.val := Nat.lt_trans Nat.zero_lt_one h1
  simp only [chainKernel]
  rw [chainCondition_predIndex (predIndex j hpos) (predIndex_pos_of_two j h1)]
  rfl

theorem threeVertex_fromPred_right_eq {S : ObservedSignature}
    (j : Fin S.count) (h1 : 1 < j.val) :
    threeVertexChainTerm j h1 =
      ProbabilityTerm.marginalize (threeVertexSummed j h1)
        (.multiply
          (.kernel ⟨NodeSet.singleton j, NodeSet.empty,
            NodeSet.union (threeVertexSummed j h1)
              (chainCondition NodeSet.full (predIndex2 j h1))⟩)
          (.multiply
            (.kernel (chainKernel NodeSet.full
              (predIndex j (Nat.lt_trans Nat.zero_lt_one h1))))
            (.kernel (chainKernel NodeSet.full (predIndex2 j h1))))) := by
  have hpos : 0 < j.val := Nat.lt_trans Nat.zero_lt_one h1
  simp only [threeVertexChainTerm, threeVertexSummed, chainKernel]
  rw [threeVertex_pa_eq j h1]
  rfl

/-- From `P(Y | Pa_V(k))` to the three-vertex chain term. Lets are
avoided so `dsimp` of `compile` sees the constructors. -/
def threeVertexFromPredDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (h1 : 1 < j.val) :
    PathDoCalculusDerivation G
      (.kernel ⟨q.outcome, NodeSet.empty,
        chainCondition NodeSet.full (predIndex2 j h1)⟩)
      (threeVertexChainTerm j h1) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (threeVertex_fromPred_left_eq q hmem h1)
    (threeVertex_fromPred_right_eq j h1)
    (DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G)
      (DoCalculusDerivation.marginalization
        (G := G) (separation := pathRuleSeparation G)
        NodeSet.empty (NodeSet.singleton j) (threeVertexSummed j h1)
        (chainCondition NodeSet.full (predIndex2 j h1))
        (threeVertexFourWayOuter j h1))
      (DoCalculusDerivation.marginalizeCongr
        (G := G) (separation := pathRuleSeparation G)
        (threeVertexSummed j h1)
        (DoCalculusDerivation.trans
          (G := G) (separation := pathRuleSeparation G)
          (DoCalculusDerivation.chain
            (G := G) (separation := pathRuleSeparation G)
            NodeSet.empty (NodeSet.singleton j) (threeVertexSummed j h1)
            (chainCondition NodeSet.full (predIndex2 j h1))
            (threeVertexFourWayOuter j h1))
          (DoCalculusDerivation.multiplyCongr
            (G := G) (separation := pathRuleSeparation G)
            (DoCalculusDerivation.refl
              (G := G) (separation := pathRuleSeparation G)
              (.kernel ⟨NodeSet.singleton j, NodeSet.empty,
                NodeSet.union (threeVertexSummed j h1)
                  (chainCondition NodeSet.full
                    (predIndex2 j h1))⟩))
            (DoCalculusDerivation.eqCongr
              (G := G) (separation := pathRuleSeparation G)
              (threeVertex_innerChainLeft_eq j h1)
              (threeVertex_innerProduct_eq j h1)
              (DoCalculusDerivation.chain
                (G := G) (separation := pathRuleSeparation G)
                NodeSet.empty
                (NodeSet.singleton
                  (predIndex j (Nat.lt_trans Nat.zero_lt_one h1)))
                (NodeSet.singleton (predIndex2 j h1))
                (chainCondition NodeSet.full (predIndex2 j h1))
                (threeVertexFourWayInner j h1)))))))

/-- Rule 2 exchange, rule 1 insert to `Pa_V(k)`, then the three-vertex
chain factorization. -/
def threeVertexIdentifiedIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (h1 : 1 < j.val)
    (hsubset :
      NodeSet.Subset q.action
        (chainCondition NodeSet.full (predIndex2 j h1)))
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (separatedInsert :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) q.outcome
        (extraPredecessors NodeSet.full (predIndex2 j h1) q.action)
        q.action) :
    PathDoCalculusDerivation G q.sourceTerm (threeVertexChainTerm j h1) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (exchangeActionRule2Derivation q separated)
    (DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G)
      (insertConditionRule1Derivation q
        (chainCondition NodeSet.full (predIndex2 j h1)) hsubset
        (threeVertex_disjoint_predecessors q hmem h1) separatedInsert)
      (threeVertexFromPredDerivation q hmem h1))

/-- Positive-class consecutive three-vertex 4.2. -/
noncomputable def threeVertexIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (obsPositive :
      forall {model : ExactModel S}, C.Mem model ->
        ObservationallyPositive model)
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (h1 : 1 < j.val)
    (hsubset :
      NodeSet.Subset q.action
        (chainCondition NodeSet.full (predIndex2 j h1)))
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (separatedInsert :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) q.outcome
        (extraPredecessors NodeSet.full (predIndex2 j h1) q.action)
        q.action) :
    PublishedJointCertificate C correct q where
  formula := threeVertexChainTerm j h1
  actionFree := threeVertexChainTerm_actionFree j h1
  derivation :=
    threeVertexIdentifiedIdDerivation q hmem h1 hsubset separated
      separatedInsert
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      threeVertexIdentifiedIdDerivation]
    let hpos : 0 < j.val := Nat.lt_trans Nat.zero_lt_one h1
    let i := predIndex j hpos
    let k := predIndex2 j h1
    let pred := chainCondition NodeSet.full k
    let summed := threeVertexSummed j h1
    let pyxSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome q.action assignment
    let predSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome pred assignment
    let hleft := JointKernelQuery.sourceTerm_eq_rule2Left_empty_xw q
    let rule2LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    let hright :=
      JointKernelQuery.observationalCondition_eq_rule2Right_empty_xw q
    let rule2RightSupported :=
      ProbabilityTerm.SupportedAt.congr hright pyxSupported
    let exchangeSupported :
        LocalDerivationSupport model assignment
          ((exchangeActionRule2Derivation q separated).compile correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        exchangeActionRule2Derivation]
      exact
        ⟨sourceSupported,
          ⟨pyxSupported,
            ⟨rule2LeftSupported, ⟨rule2RightSupported, ()⟩⟩⟩⟩
    let hrule1Right := insertCondition_rule1Right_eq q pred
    let hrule1Left := insertCondition_rule1Left_eq q hsubset
    let rule1RightSupported :=
      ProbabilityTerm.SupportedAt.congr hrule1Right pyxSupported
    let rule1LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hrule1Left predSupported
    let insertSupported :
        LocalDerivationSupport model assignment
          ((insertConditionRule1Derivation q pred hsubset
            (threeVertex_disjoint_predecessors q hmem h1)
            separatedInsert).compile correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        insertConditionRule1Derivation]
      exact
        ⟨pyxSupported,
          ⟨predSupported,
            ⟨rule1RightSupported,
              ⟨rule1LeftSupported,
                ⟨rule1LeftSupported, ⟨rule1RightSupported, ()⟩⟩⟩⟩⟩⟩
    let hy : q.outcome = NodeSet.singleton j :=
      NodeSet.eq_singleton_of_members hmem
    let predSingletonSupported' :=
      ProbabilityTerm.SupportedAt.congr (by rw [hy]) predSupported
    let kjSupported (variant : S.Assignment) :=
      observationalConditional_supportedAt model (obsPositive member)
        (NodeSet.singleton j)
        (NodeSet.union summed pred) variant
    let kiSupported (variant : S.Assignment) :=
      observationalConditional_supportedAt model (obsPositive member)
        (NodeSet.singleton i)
        (NodeSet.union (NodeSet.singleton k) pred) variant
    let kkSupported (variant : S.Assignment) :=
      observationalConditional_supportedAt model (obsPositive member)
        (NodeSet.singleton k) pred variant
    let innerProductSupported (variant : S.Assignment) :=
      ProbabilityTerm.multiply_supportedAt
        (kiSupported variant) (kkSupported variant)
    let chainInnerProductSupported (variant : S.Assignment) :=
      ProbabilityTerm.multiply_supportedAt
        (observationalConditional_supportedAt model (obsPositive member)
          (NodeSet.singleton i) (chainCondition NodeSet.full i) variant)
        (observationalConditional_supportedAt model (obsPositive member)
          (NodeSet.singleton k) (chainCondition NodeSet.full k) variant)
    let summedKernelSupported (variant : S.Assignment) :=
      observationalConditional_supportedAt model (obsPositive member)
        summed pred variant
    let summedUnionKernelSupported (variant : S.Assignment) :=
      ProbabilityTerm.SupportedAt.congr
        (threeVertex_innerChainLeft_eq j h1)
        (summedKernelSupported variant)
    let chainRightSupported (variant : S.Assignment) :=
      ProbabilityTerm.multiply_supportedAt
        (kjSupported variant) (summedKernelSupported variant)
    let multiplyCongrRightSupported (variant : S.Assignment) :=
      ProbabilityTerm.multiply_supportedAt
        (kjSupported variant) (chainInnerProductSupported variant)
    let jointSupported (variant : S.Assignment) :=
      observationalConditional_supportedAt model (obsPositive member)
        (NodeSet.union (NodeSet.singleton j) summed) pred variant
    let formulaSupported' :
        (threeVertexChainTerm j h1).SupportedAt model assignment := by
      simpa [threeVertexChainTerm, ProbabilityTerm.denote] using
        ProbabilityResult.sum_map_supported
          (ProbabilityTerm.marginalAssignments S summed assignment)
          (fun variant =>
            (ProbabilityTerm.multiply
              (.kernel (chainKernel NodeSet.full j))
              (.multiply
                (.kernel (chainKernel NodeSet.full i))
                (.kernel (chainKernel NodeSet.full k)))).denote
              model variant)
          (fun variant =>
            ProbabilityTerm.multiply_supportedAt
              (observationalConditional_supportedAt model
                (obsPositive member) (NodeSet.singleton j)
                (chainCondition NodeSet.full j) variant)
              (ProbabilityTerm.multiply_supportedAt
                (observationalConditional_supportedAt model
                  (obsPositive member) (NodeSet.singleton i)
                  (chainCondition NodeSet.full i) variant)
                (observationalConditional_supportedAt model
                  (obsPositive member) (NodeSet.singleton k)
                  (chainCondition NodeSet.full k) variant)))
    let innerRightSupported :=
      ProbabilityTerm.SupportedAt.congr
        (threeVertex_fromPred_right_eq j h1) formulaSupported'
    let jointMargSupported := by
      simpa [ProbabilityTerm.denote] using
        ProbabilityResult.sum_map_supported
          (ProbabilityTerm.marginalAssignments S summed assignment)
          (fun variant =>
            (ProbabilityTerm.kernel
              ⟨NodeSet.union (NodeSet.singleton j) summed,
                NodeSet.empty, pred⟩).denote model variant)
          (fun variant => jointSupported variant)
    let fromPredSupported :
        LocalDerivationSupport model assignment
          ((threeVertexFromPredDerivation q hmem h1).compile correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        threeVertexFromPredDerivation]
      exact
        ⟨predSupported,
          ⟨formulaSupported',
            ⟨predSingletonSupported',
              ⟨innerRightSupported,
                ⟨⟨predSingletonSupported', ⟨jointMargSupported, ()⟩⟩,
                  ⟨jointMargSupported,
                    ⟨innerRightSupported,
                      fun variant _hv =>
                        ⟨jointSupported variant,
                          ⟨multiplyCongrRightSupported variant,
                            ⟨⟨jointSupported variant,
                                ⟨chainRightSupported variant, ()⟩⟩,
                              ⟨chainRightSupported variant,
                                ⟨multiplyCongrRightSupported variant,
                                  ⟨⟨kjSupported variant,
                                      ⟨kjSupported variant, ()⟩⟩,
                                    ⟨summedKernelSupported variant,
                                      ⟨chainInnerProductSupported variant,
                                        ⟨summedUnionKernelSupported variant,
                                          ⟨innerProductSupported variant,
                                            ()⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    exact
      ⟨sourceSupported,
        ⟨formulaSupported',
          ⟨exchangeSupported,
            ⟨pyxSupported,
              ⟨formulaSupported',
                ⟨insertSupported, fromPredSupported⟩⟩⟩⟩⟩⟩

/-- Boolean consecutive three-vertex 4.2 unpacks on the positive class. -/
noncomputable def threeVertexIdentifiedPublishedCertificate?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  match hmem : NodeSet.members q.outcome with
  | [j] =>
      if h1 : 1 < j.val then
        if hsub :
            NodeSet.subsetBool q.action
              (chainCondition NodeSet.full (predIndex2 j h1)) = true then
          if h : G.dSeparated
              (GraphMutilation.barUnderline NodeSet.empty q.action)
              q.outcome q.action NodeSet.empty = true then
            let extra :=
              extraPredecessors NodeSet.full (predIndex2 j h1) q.action
            let hsubset :=
              (NodeSet.subsetBool_eq_true_iff q.action
                (chainCondition NodeSet.full (predIndex2 j h1))).mp hsub
            if hW : NodeSet.isEmpty extra = true then
              some
                (threeVertexIdentifiedPublishedCertificate
                  (C := GraphModelClass.positive G)
                  (fun {model}
                      (member : (GraphModelClass.positive G).Mem model) =>
                    member.2)
                  correct q hmem h1 hsubset
                  (correct.pathDSeparated_of_dSeparated h)
                  (PathSpecification.PathDSeparated.of_isEmpty_right G
                    (GraphMutilation.bar NodeSet.empty) q.outcome extra
                    q.action hW))
            else if hins : G.dSeparated
                (GraphMutilation.bar NodeSet.empty) q.outcome extra
                q.action = true then
              some
                (threeVertexIdentifiedPublishedCertificate
                  (C := GraphModelClass.positive G)
                  (fun {model}
                      (member : (GraphModelClass.positive G).Mem model) =>
                    member.2)
                  correct q hmem h1 hsubset
                  (correct.pathDSeparated_of_dSeparated h)
                  (correct.pathDSeparated_of_dSeparated hins))
            else
              none
          else
            none
        else
          none
      else
        none
  | _ => none

/-- Empty-action four-way split of `{j}` against its n predecessors
and the chain-rule conditioner of the earliest of those. -/
def consecutiveFourWay {S : ObservedSignature} (j : Fin S.count)
    (n : Nat) (h : n ≤ j.val) :
    FourWayDisjoint NodeSet.empty (NodeSet.singleton j)
      (consecutiveSummed j n h)
      (chainCondition NodeSet.full (predIndexNth j n h)) :=
  FourWayDisjoint.emptyAction _ _ _
    (disjoint_singleton_consecutiveSummed j n h)
    (by
      cases n with
      | zero =>
          simpa [predIndexNth_eq_zero] using
            disjoint_singleton_chainCondition NodeSet.full j
      | succ n =>
          exact disjoint_later_chainCondition NodeSet.full
            (predIndexNth_lt_of_pos j (n + 1) h (Nat.succ_pos _)))
    (disjoint_consecutiveSummed_chainCondition j n h)

theorem consecutiveProduct_left_zero {S : ObservedSignature}
    (j : Fin S.count) (h : 0 ≤ j.val) :
    ProbabilityTerm.kernel
        ⟨consecutiveInterval j 0 h, NodeSet.empty,
          chainCondition NodeSet.full (predIndexNth j 0 h)⟩ =
      .kernel (chainKernel NodeSet.full j) := by
  simp [consecutiveInterval_zero, predIndexNth_eq_zero, chainKernel]

theorem consecutive_product_succ_eq {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n + 1 ≤ j.val) :
    productTerms (consecutiveChainKernels j (n + 1) h) =
      .multiply
        (.kernel (chainKernel NodeSet.full j))
        (productTerms
          (consecutiveChainKernels
            (predIndexNth j 1 (one_le_of_succ_le h)) n
            (by
              simpa [predIndexNth] using
                Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h)))) := by
  rw [consecutiveChainKernels_succ,
    productTerms_cons _ _ (consecutiveChainKernels_ne_nil _ _ _)]

theorem consecutiveProduct_inner_left_eq {S : ObservedSignature}
    (j : Fin S.count) (n : Nat) (h : n + 1 ≤ j.val) :
    ProbabilityTerm.kernel
        ⟨consecutiveSummed j (n + 1) h, NodeSet.empty,
          chainCondition NodeSet.full (predIndexNth j (n + 1) h)⟩ =
      .kernel ⟨
        consecutiveInterval (predIndexNth j 1 (one_le_of_succ_le h)) n
          (by
            simpa [predIndexNth] using
              Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h)),
        NodeSet.empty,
        chainCondition NodeSet.full
          (predIndexNth (predIndexNth j 1 (one_le_of_succ_le h)) n
            (by
              simpa [predIndexNth] using
                Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h)))⟩ := by
  rw [consecutiveSummed_succ_eq_interval, predIndexNth_predIndexNth_one]

/-- Base: a one-vertex interval is the single chain-rule kernel. -/
def consecutiveProductDerivation_zero {S : ObservedSignature}
    {G : ObservedGraph S} (j : Fin S.count) (hn : 0 ≤ j.val) :
    PathDoCalculusDerivation G
      (.kernel ⟨consecutiveInterval j 0 hn, NodeSet.empty,
        chainCondition NodeSet.full (predIndexNth j 0 hn)⟩)
      (productTerms (consecutiveChainKernels j 0 hn)) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (consecutiveProduct_left_zero j hn)
    (consecutiveChainKernels_product_zero j hn)
    (DoCalculusDerivation.refl
      (G := G) (separation := pathRuleSeparation G)
      (.kernel (chainKernel NodeSet.full j)))

/-- Step: split off `j`, then recurse on the earlier interval. -/
def consecutiveProductDerivation_succ {S : ObservedSignature}
    {G : ObservedGraph S} (j : Fin S.count) (n : Nat)
    (hn : n + 1 ≤ j.val)
    (inner :
      PathDoCalculusDerivation G
        (.kernel ⟨
          consecutiveInterval (predIndexNth j 1 (one_le_of_succ_le hn)) n
            (by
              simpa [predIndexNth] using
                Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn)),
          NodeSet.empty,
          chainCondition NodeSet.full
            (predIndexNth (predIndexNth j 1 (one_le_of_succ_le hn)) n
              (by
                simpa [predIndexNth] using
                  Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn)))⟩)
        (productTerms
          (consecutiveChainKernels
            (predIndexNth j 1 (one_le_of_succ_le hn)) n
            (by
              simpa [predIndexNth] using
                Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn))))) :
    PathDoCalculusDerivation G
      (.kernel ⟨consecutiveInterval j (n + 1) hn, NodeSet.empty,
        chainCondition NodeSet.full (predIndexNth j (n + 1) hn)⟩)
      (productTerms (consecutiveChainKernels j (n + 1) hn)) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (show ProbabilityTerm.kernel
        ⟨consecutiveInterval j (n + 1) hn, NodeSet.empty,
          chainCondition NodeSet.full (predIndexNth j (n + 1) hn)⟩ =
        .kernel ⟨NodeSet.union (NodeSet.singleton j)
            (consecutiveSummed j (n + 1) hn),
          NodeSet.empty,
          chainCondition NodeSet.full (predIndexNth j (n + 1) hn)⟩ from
      rfl)
    (consecutive_product_succ_eq j n hn)
    (DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G)
      (DoCalculusDerivation.chain
        (G := G) (separation := pathRuleSeparation G)
        NodeSet.empty (NodeSet.singleton j)
        (consecutiveSummed j (n + 1) hn)
        (chainCondition NodeSet.full (predIndexNth j (n + 1) hn))
        (consecutiveFourWay j (n + 1) hn))
      (DoCalculusDerivation.multiplyCongr
        (G := G) (separation := pathRuleSeparation G)
        (DoCalculusDerivation.eqCongr
          (G := G) (separation := pathRuleSeparation G)
          (consecutive_chainKernel_eq j (n + 1) hn)
          rfl
          (DoCalculusDerivation.refl
            (G := G) (separation := pathRuleSeparation G)
            (.kernel (chainKernel NodeSet.full j))))
        (DoCalculusDerivation.eqCongr
          (G := G) (separation := pathRuleSeparation G)
          (consecutiveProduct_inner_left_eq j n hn)
          rfl
          inner)))

/-- Factor the joint on `{j}` together with its n predecessors into the
later-first product of chain-rule kernels. Recurses on the earlier
interval so the derivation tree has depth `n`. -/
def consecutiveProductDerivation {S : ObservedSignature} {G : ObservedGraph S}
    (j : Fin S.count) (n : Nat) (hn : n ≤ j.val) :
    PathDoCalculusDerivation G
      (.kernel ⟨consecutiveInterval j n hn, NodeSet.empty,
        chainCondition NodeSet.full (predIndexNth j n hn)⟩)
      (productTerms (consecutiveChainKernels j n hn)) :=
  match n with
  | 0 => consecutiveProductDerivation_zero j hn
  | n + 1 =>
      consecutiveProductDerivation_succ j n hn
        (consecutiveProductDerivation
          (predIndexNth j 1 (one_le_of_succ_le hn)) n
          (by
            simpa [predIndexNth] using
              Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn)))
termination_by n

theorem consecutiveFromPred_left_eq (q : JointKernelQuery S)
    {j : Fin S.count} (hmem : NodeSet.members q.outcome = [j])
    (n : Nat) (hn : n ≤ j.val) :
    ProbabilityTerm.kernel
        ⟨q.outcome, NodeSet.empty,
          chainCondition NodeSet.full (predIndexNth j n hn)⟩ =
      .kernel ⟨NodeSet.singleton j, NodeSet.empty,
        chainCondition NodeSet.full (predIndexNth j n hn)⟩ := by
  rw [NodeSet.eq_singleton_of_members hmem]

theorem consecutiveFromPred_zero_eq (q : JointKernelQuery S)
    {j : Fin S.count} (hmem : NodeSet.members q.outcome = [j])
    (hn : 0 ≤ j.val) :
    ProbabilityTerm.kernel
        ⟨q.outcome, NodeSet.empty,
          chainCondition NodeSet.full (predIndexNth j 0 hn)⟩ =
      .kernel (chainKernel NodeSet.full j) := by
  rw [NodeSet.eq_singleton_of_members hmem, predIndexNth_eq_zero]
  simp [chainKernel]

/-- From `P(Y | Pa_V(j))` to the singleton chain-rule kernel. -/
def consecutiveFromPredDerivation_zero {S : ObservedSignature}
    {G : ObservedGraph S} (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (hn : 0 ≤ j.val) :
    PathDoCalculusDerivation G
      (.kernel ⟨q.outcome, NodeSet.empty,
        chainCondition NodeSet.full (predIndexNth j 0 hn)⟩)
      (consecutiveChainTerm j 0 hn) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (consecutiveFromPred_zero_eq q hmem hn)
    (consecutiveChainTerm_zero j)
    (DoCalculusDerivation.refl
      (G := G) (separation := pathRuleSeparation G)
      (.kernel (chainKernel NodeSet.full j)))

/-- From `P(Y | Pa_V(j - (n+1)))` to the complementary sum of the
later-first chain product. -/
def consecutiveFromPredDerivation_succ {S : ObservedSignature}
    {G : ObservedGraph S} (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (n : Nat)
    (hn : n + 1 ≤ j.val) :
    PathDoCalculusDerivation G
      (.kernel ⟨q.outcome, NodeSet.empty,
        chainCondition NodeSet.full (predIndexNth j (n + 1) hn)⟩)
      (consecutiveChainTerm j (n + 1) hn) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (consecutiveFromPred_left_eq q hmem (n + 1) hn)
    (consecutiveChainTerm_succ j n hn)
    (DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G)
      (DoCalculusDerivation.marginalization
        (G := G) (separation := pathRuleSeparation G)
        NodeSet.empty (NodeSet.singleton j)
        (consecutiveSummed j (n + 1) hn)
        (chainCondition NodeSet.full (predIndexNth j (n + 1) hn))
        (consecutiveFourWay j (n + 1) hn))
      (DoCalculusDerivation.marginalizeCongr
        (G := G) (separation := pathRuleSeparation G)
        (consecutiveSummed j (n + 1) hn)
        (DoCalculusDerivation.eqCongr
          (G := G) (separation := pathRuleSeparation G)
          (show ProbabilityTerm.kernel
              ⟨consecutiveInterval j (n + 1) hn, NodeSet.empty,
                chainCondition NodeSet.full
                  (predIndexNth j (n + 1) hn)⟩ =
            .kernel ⟨NodeSet.union (NodeSet.singleton j)
                (consecutiveSummed j (n + 1) hn),
              NodeSet.empty,
              chainCondition NodeSet.full
                (predIndexNth j (n + 1) hn)⟩ from
            rfl)
          (consecutive_product_succ_eq j n hn).symm
          (consecutiveProductDerivation j (n + 1) hn))))

/-- From `P(Y | Pa_V(j - n))` to the consecutive n-step chain term.
The `n = 0` case is the singleton kernel; otherwise an empty-action
complementary sum of `consecutiveProductDerivation`. -/
def consecutiveFromPredDerivation {S : ObservedSignature}
    {G : ObservedGraph S} (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (n : Nat) (hn : n ≤ j.val) :
    PathDoCalculusDerivation G
      (.kernel ⟨q.outcome, NodeSet.empty,
        chainCondition NodeSet.full (predIndexNth j n hn)⟩)
      (consecutiveChainTerm j n hn) :=
  match n with
  | 0 => consecutiveFromPredDerivation_zero q hmem hn
  | n + 1 => consecutiveFromPredDerivation_succ q hmem n hn

theorem consecutive_disjoint_predecessors
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (n : Nat) (hn : n ≤ j.val) :
    NodeSet.Disjoint q.outcome
      (chainCondition NodeSet.full (predIndexNth j n hn)) := by
  cases n with
  | zero =>
      have hj : q.outcome = NodeSet.singleton j :=
        NodeSet.eq_singleton_of_members hmem
      simpa [hj, predIndexNth_eq_zero] using
        disjoint_singleton_chainCondition NodeSet.full j
  | succ n =>
      exact (NodeSet.eq_singleton_of_members hmem) ▸
        disjoint_later_chainCondition NodeSet.full
          (predIndexNth_lt_of_pos j (n + 1) hn (Nat.succ_pos _))

/-- The later-first chain product is defined in every observationally
positive model: each factor is an observational conditional. -/
noncomputable def consecutiveChainProduct_supportedAt
    {model : FiniteLatentSCM S} (positive : ObservationallyPositive model)
    (j : Fin S.count) (n : Nat) (hn : n ≤ j.val) (assignment : S.Assignment) :
    (productTerms (consecutiveChainKernels j n hn)).SupportedAt
      model assignment :=
  match n with
  | 0 =>
      ProbabilityTerm.SupportedAt.congr
        (consecutiveChainKernels_product_zero j hn).symm
        (observationalConditional_supportedAt model positive
          (NodeSet.singleton j) (chainCondition NodeSet.full j) assignment)
  | n + 1 =>
      ProbabilityTerm.SupportedAt.congr
        (consecutive_product_succ_eq j n hn).symm
        (ProbabilityTerm.multiply_supportedAt
          (observationalConditional_supportedAt model positive
            (NodeSet.singleton j) (chainCondition NodeSet.full j)
            assignment)
          (consecutiveChainProduct_supportedAt positive
            (predIndexNth j 1 (one_le_of_succ_le hn)) n
            (by
              simpa [predIndexNth] using
                Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn))
            assignment))
termination_by n

/-- Recursive support tree of `consecutiveProductDerivation`. -/
noncomputable def consecutiveProductSupported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    {model : FiniteLatentSCM S} (positive : ObservationallyPositive model)
    (assignment : S.Assignment) (j : Fin S.count) (n : Nat)
    (hn : n ≤ j.val) :
    LocalDerivationSupport model assignment
      ((consecutiveProductDerivation (G := G) j n hn).compile correct) := by
  match n with
  | 0 =>
      let kj :=
        observationalConditional_supportedAt model positive
          (NodeSet.singleton j) (chainCondition NodeSet.full j) assignment
      let intervalSupported :=
        ProbabilityTerm.SupportedAt.congr
          (consecutiveProduct_left_zero j hn).symm kj
      let productSupported :=
        ProbabilityTerm.SupportedAt.congr
          (consecutiveChainKernels_product_zero j hn).symm kj
      let supportZero :
          LocalDerivationSupport model assignment
            ((consecutiveProductDerivation_zero (G := G) j hn).compile
              correct) := by
        dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
          consecutiveProductDerivation_zero]
        exact ⟨intervalSupported, ⟨productSupported, ⟨kj, ⟨kj, ()⟩⟩⟩⟩
      have hder :
          consecutiveProductDerivation (G := G) j 0 hn =
            consecutiveProductDerivation_zero (G := G) j hn := by
        simp [consecutiveProductDerivation]
      exact hder ▸ supportZero
  | n + 1 =>
      let h1 : 1 ≤ j.val := one_le_of_succ_le hn
      let pred1 := predIndexNth j 1 h1
      let hn' : n ≤ pred1.val := by
        simpa [predIndexNth] using
          Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn)
      let paEarliest :=
        chainCondition NodeSet.full (predIndexNth j (n + 1) hn)
      let summed := consecutiveSummed j (n + 1) hn
      let kj :=
        observationalConditional_supportedAt model positive
          (NodeSet.singleton j) (chainCondition NodeSet.full j) assignment
      let unfoldedKj :=
        ProbabilityTerm.SupportedAt.congr
          (consecutive_chainKernel_eq j (n + 1) hn).symm kj
      let innerProduct :=
        consecutiveChainProduct_supportedAt positive pred1 n hn' assignment
      let productAll :=
        ProbabilityTerm.SupportedAt.congr
          (consecutive_product_succ_eq j n hn).symm
          (ProbabilityTerm.multiply_supportedAt kj innerProduct)
      let intervalSupported :=
        observationalConditional_supportedAt model positive
          (consecutiveInterval j (n + 1) hn) paEarliest assignment
      let jointSupported :=
        observationalConditional_supportedAt model positive
          (NodeSet.union (NodeSet.singleton j) summed) paEarliest assignment
      let summedSupported :=
        observationalConditional_supportedAt model positive
          summed paEarliest assignment
      let innerLeftSupported :=
        ProbabilityTerm.SupportedAt.congr
          (consecutiveProduct_inner_left_eq j n hn) summedSupported
      let chainRightSupported :=
        ProbabilityTerm.multiply_supportedAt unfoldedKj summedSupported
      let multiplyRightSupported :=
        ProbabilityTerm.multiply_supportedAt kj innerProduct
      let innerSupported :=
        consecutiveProductSupported correct positive assignment
          (predIndexNth j 1 (one_le_of_succ_le hn)) n
          (by
            simpa [predIndexNth] using
              Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn))
      let supportSucc :
          LocalDerivationSupport model assignment
            ((consecutiveProductDerivation_succ (G := G) j n hn
              (consecutiveProductDerivation (G := G)
                (predIndexNth j 1 (one_le_of_succ_le hn)) n
                (by
                  simpa [predIndexNth] using
                    Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn)))).compile
              correct) := by
        dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
          consecutiveProductDerivation_succ]
        exact
          ⟨intervalSupported,
            ⟨productAll,
              ⟨jointSupported,
                ⟨multiplyRightSupported,
                  ⟨⟨jointSupported, ⟨chainRightSupported, ()⟩⟩,
                    ⟨chainRightSupported,
                      ⟨multiplyRightSupported,
                        ⟨⟨unfoldedKj, ⟨kj, ⟨kj, ⟨kj, ()⟩⟩⟩⟩,
                          ⟨summedSupported,
                            ⟨innerProduct, innerSupported⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
      have hder :
          consecutiveProductDerivation (G := G) j (n + 1) hn =
            consecutiveProductDerivation_succ (G := G) j n hn
              (consecutiveProductDerivation (G := G)
                (predIndexNth j 1 (one_le_of_succ_le hn)) n
                (by
                  simpa [predIndexNth] using
                    Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn))) := by
        simp [consecutiveProductDerivation]
      exact hder ▸ supportSucc
termination_by n

/-- Recursive support tree of `consecutiveFromPredDerivation`. -/
noncomputable def consecutiveFromPredSupported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    {model : FiniteLatentSCM S} (positive : ObservationallyPositive model)
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (n : Nat) (hn : n ≤ j.val)
    (assignment : S.Assignment) :
    LocalDerivationSupport model assignment
      ((consecutiveFromPredDerivation (G := G) q hmem n hn).compile
        correct) := by
  match n with
  | 0 =>
      let kj :=
        observationalConditional_supportedAt model positive
          (NodeSet.singleton j) (chainCondition NodeSet.full j) assignment
      let predSupported :=
        ProbabilityTerm.SupportedAt.congr
          (consecutiveFromPred_zero_eq q hmem hn).symm kj
      let supportZero :
          LocalDerivationSupport model assignment
            ((consecutiveFromPredDerivation_zero (G := G) q hmem hn).compile
              correct) := by
        dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
          consecutiveFromPredDerivation_zero]
        exact ⟨predSupported, ⟨kj, ⟨kj, ⟨kj, ()⟩⟩⟩⟩
      have hder :
          consecutiveFromPredDerivation (G := G) q hmem 0 hn =
            consecutiveFromPredDerivation_zero (G := G) q hmem hn := by
        simp [consecutiveFromPredDerivation]
      exact hder ▸ supportZero
  | n + 1 =>
      let paEarliest :=
        chainCondition NodeSet.full (predIndexNth j (n + 1) hn)
      let summed := consecutiveSummed j (n + 1) hn
      let predSupported :=
        observationalConditional_supportedAt model positive
          q.outcome paEarliest assignment
      let predSingletonSupported :=
        observationalConditional_supportedAt model positive
          (NodeSet.singleton j) paEarliest assignment
      let predSingletonSupported' :=
        ProbabilityTerm.SupportedAt.congr
          (consecutiveFromPred_left_eq q hmem (n + 1) hn) predSupported
      let jointSupported :=
        observationalConditional_supportedAt model positive
          (NodeSet.union (NodeSet.singleton j) summed) paEarliest assignment
      let intervalSupported :=
        observationalConditional_supportedAt model positive
          (consecutiveInterval j (n + 1) hn) paEarliest assignment
      let kj :=
        observationalConditional_supportedAt model positive
          (NodeSet.singleton j) (chainCondition NodeSet.full j) assignment
      let innerProduct :=
        consecutiveChainProduct_supportedAt positive
          (predIndexNth j 1 (one_le_of_succ_le hn)) n
          (by
            simpa [predIndexNth] using
              Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn))
          assignment
      let multiplyRightSupported :=
        ProbabilityTerm.multiply_supportedAt kj innerProduct
      let formulaSupported :
          (consecutiveChainTerm j (n + 1) hn).SupportedAt model assignment := by
        simpa [consecutiveChainTerm_succ j n hn, ProbabilityTerm.denote] using
          ProbabilityResult.sum_map_supported
            (ProbabilityTerm.marginalAssignments S summed assignment)
            (fun variant =>
              (ProbabilityTerm.multiply
                (.kernel (chainKernel NodeSet.full j))
                (productTerms
                  (consecutiveChainKernels
                    (predIndexNth j 1 (one_le_of_succ_le hn)) n
                    (by
                      simpa [predIndexNth] using
                        Nat.le_sub_one_of_lt
                          (Nat.lt_of_succ_le hn))))).denote
                model variant)
            (fun variant =>
              ProbabilityTerm.multiply_supportedAt
                (observationalConditional_supportedAt model positive
                  (NodeSet.singleton j) (chainCondition NodeSet.full j)
                  variant)
                (consecutiveChainProduct_supportedAt positive
                  (predIndexNth j 1 (one_le_of_succ_le hn)) n
                  (by
                    simpa [predIndexNth] using
                      Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn))
                  variant))
      let jointMargSupported := by
        simpa [ProbabilityTerm.denote] using
          ProbabilityResult.sum_map_supported
            (ProbabilityTerm.marginalAssignments S summed assignment)
            (fun variant =>
              (ProbabilityTerm.kernel
                ⟨NodeSet.union (NodeSet.singleton j) summed,
                  NodeSet.empty, paEarliest⟩).denote model variant)
            (fun variant =>
              observationalConditional_supportedAt model positive
                (NodeSet.union (NodeSet.singleton j) summed) paEarliest
                variant)
      let innerRightSupported :=
        ProbabilityTerm.SupportedAt.congr
          (consecutiveChainTerm_succ j n hn) formulaSupported
      let supportSucc :
          LocalDerivationSupport model assignment
            ((consecutiveFromPredDerivation_succ (G := G) q hmem n hn).compile
              correct) := by
        dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
          consecutiveFromPredDerivation_succ]
        exact
          ⟨predSupported,
            ⟨formulaSupported,
              ⟨predSingletonSupported',
                ⟨innerRightSupported,
                  ⟨⟨predSingletonSupported', ⟨jointMargSupported, ()⟩⟩,
                    ⟨jointMargSupported,
                      ⟨innerRightSupported,
                        fun variant _hv =>
                          ⟨observationalConditional_supportedAt model positive
                              (consecutiveInterval j (n + 1) hn) paEarliest
                              variant,
                            ⟨ProbabilityTerm.multiply_supportedAt
                                (observationalConditional_supportedAt model
                                  positive (NodeSet.singleton j)
                                  (chainCondition NodeSet.full j) variant)
                                (consecutiveChainProduct_supportedAt positive
                                  (predIndexNth j 1 (one_le_of_succ_le hn)) n
                                  (by
                                    simpa [predIndexNth] using
                                      Nat.le_sub_one_of_lt
                                        (Nat.lt_of_succ_le hn))
                                  variant),
                              consecutiveProductSupported correct positive
                                variant j (n + 1) hn⟩⟩⟩⟩⟩⟩⟩⟩⟩
      have hder :
          consecutiveFromPredDerivation (G := G) q hmem (n + 1) hn =
            consecutiveFromPredDerivation_succ (G := G) q hmem n hn := by
        simp [consecutiveFromPredDerivation]
      exact hder ▸ supportSucc

/-- Rule 2 exchange, rule 1 insert to `Pa_V(j - n)`, then the consecutive
n-step chain factorization. -/
def consecutiveIdentifiedIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (n : Nat) (hn : n ≤ j.val)
    (hsubset :
      NodeSet.Subset q.action
        (chainCondition NodeSet.full (predIndexNth j n hn)))
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (separatedInsert :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) q.outcome
        (extraPredecessors NodeSet.full (predIndexNth j n hn) q.action)
        q.action) :
    PathDoCalculusDerivation G q.sourceTerm (consecutiveChainTerm j n hn) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (exchangeActionRule2Derivation q separated)
    (DoCalculusDerivation.trans
      (G := G) (separation := pathRuleSeparation G)
      (insertConditionRule1Derivation q
        (chainCondition NodeSet.full (predIndexNth j n hn)) hsubset
        (consecutive_disjoint_predecessors q hmem n hn) separatedInsert)
      (consecutiveFromPredDerivation q hmem n hn))

/-- Positive-class consecutive n-step 4.2. -/
noncomputable def consecutiveIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (obsPositive :
      forall {model : ExactModel S}, C.Mem model ->
        ObservationallyPositive model)
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (n : Nat) (hn : n ≤ j.val)
    (hsubset :
      NodeSet.Subset q.action
        (chainCondition NodeSet.full (predIndexNth j n hn)))
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline NodeSet.empty q.action)
        q.outcome q.action NodeSet.empty)
    (separatedInsert :
      PathSpecification.PathDSeparated G
        (GraphMutilation.bar NodeSet.empty) q.outcome
        (extraPredecessors NodeSet.full (predIndexNth j n hn) q.action)
        q.action) :
    PublishedJointCertificate C correct q where
  formula := consecutiveChainTerm j n hn
  actionFree := consecutiveChainTerm_actionFree j n hn
  derivation :=
    consecutiveIdentifiedIdDerivation q hmem n hn hsubset separated
      separatedInsert
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      consecutiveIdentifiedIdDerivation]
    let pred := chainCondition NodeSet.full (predIndexNth j n hn)
    let pyxSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome q.action assignment
    let predSupported :=
      observationalConditional_supportedAt model (obsPositive member)
        q.outcome pred assignment
    let formulaSupported :=
      (consecutiveFromPredSupported correct (obsPositive member) q hmem n hn
        assignment).endpoints.2
    let hleft := JointKernelQuery.sourceTerm_eq_rule2Left_empty_xw q
    let rule2LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    let hright :=
      JointKernelQuery.observationalCondition_eq_rule2Right_empty_xw q
    let rule2RightSupported :=
      ProbabilityTerm.SupportedAt.congr hright pyxSupported
    let exchangeSupported :
        LocalDerivationSupport model assignment
          ((exchangeActionRule2Derivation q separated).compile correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        exchangeActionRule2Derivation]
      exact
        ⟨sourceSupported,
          ⟨pyxSupported,
            ⟨rule2LeftSupported, ⟨rule2RightSupported, ()⟩⟩⟩⟩
    let hrule1Right := insertCondition_rule1Right_eq q pred
    let hrule1Left := insertCondition_rule1Left_eq q hsubset
    let rule1RightSupported :=
      ProbabilityTerm.SupportedAt.congr hrule1Right pyxSupported
    let rule1LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hrule1Left predSupported
    let insertSupported :
        LocalDerivationSupport model assignment
          ((insertConditionRule1Derivation q pred hsubset
            (consecutive_disjoint_predecessors q hmem n hn)
            separatedInsert).compile correct) := by
      dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
        insertConditionRule1Derivation]
      exact
        ⟨pyxSupported,
          ⟨predSupported,
            ⟨rule1RightSupported,
              ⟨rule1LeftSupported,
                ⟨rule1LeftSupported, ⟨rule1RightSupported, ()⟩⟩⟩⟩⟩⟩
    let fromPredSupported :=
      consecutiveFromPredSupported correct (obsPositive member) q hmem n hn
        assignment
    exact
      ⟨sourceSupported,
        ⟨formulaSupported,
          ⟨exchangeSupported,
            ⟨pyxSupported,
              ⟨formulaSupported,
                ⟨insertSupported, fromPredSupported⟩⟩⟩⟩⟩⟩

/-- Try consecutive n-step 4.2, largest `n` first so a longer predecessor
block is not stolen by a shorter packer whose extra vertices still
lie on a directed path. -/
noncomputable def consecutiveIdentifiedPublishedCertificateFrom?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) {j : Fin S.count}
    (hmem : NodeSet.members q.outcome = [j]) (n : Nat) (hn : n ≤ j.val) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  match n with
  | 0 => none
  | n + 1 =>
      if hsub :
          NodeSet.subsetBool q.action
            (chainCondition NodeSet.full
              (predIndexNth j (n + 1) hn)) = true then
        if h : G.dSeparated
            (GraphMutilation.barUnderline NodeSet.empty q.action)
            q.outcome q.action NodeSet.empty = true then
          let extra :=
            extraPredecessors NodeSet.full
              (predIndexNth j (n + 1) hn) q.action
          let hsubset :=
            (NodeSet.subsetBool_eq_true_iff q.action
              (chainCondition NodeSet.full
                (predIndexNth j (n + 1) hn))).mp hsub
          if hW : NodeSet.isEmpty extra = true then
            some
              (consecutiveIdentifiedPublishedCertificate
                (C := GraphModelClass.positive G)
                (fun {model}
                    (member : (GraphModelClass.positive G).Mem model) =>
                  member.2)
                correct q hmem (n + 1) hn hsubset
                (correct.pathDSeparated_of_dSeparated h)
                (PathSpecification.PathDSeparated.of_isEmpty_right G
                  (GraphMutilation.bar NodeSet.empty) q.outcome extra
                  q.action hW))
          else if hins : G.dSeparated
              (GraphMutilation.bar NodeSet.empty) q.outcome extra
              q.action = true then
            some
              (consecutiveIdentifiedPublishedCertificate
                (C := GraphModelClass.positive G)
                (fun {model}
                    (member : (GraphModelClass.positive G).Mem model) =>
                  member.2)
                correct q hmem (n + 1) hn hsubset
                (correct.pathDSeparated_of_dSeparated h)
                (correct.pathDSeparated_of_dSeparated hins))
          else
            consecutiveIdentifiedPublishedCertificateFrom? correct q hmem n
              (Nat.le_trans (Nat.le_succ n) hn)
        else
          consecutiveIdentifiedPublishedCertificateFrom? correct q hmem n
            (Nat.le_trans (Nat.le_succ n) hn)
      else
        consecutiveIdentifiedPublishedCertificateFrom? correct q hmem n
          (Nat.le_trans (Nat.le_succ n) hn)
termination_by n

/-- Boolean consecutive n-step 4.2 unpacks on the positive class. -/
noncomputable def consecutiveIdentifiedPublishedCertificate?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  match hmem : NodeSet.members q.outcome with
  | [j] =>
      consecutiveIdentifiedPublishedCertificateFrom? correct q hmem j.val
        (Nat.le_refl j.val)
  | _ => none

/-- Positive-class joint packer: complementary-marginal ID, then
singleton 4.2, consecutive n-step 4.2 (including the former two- and
three-vertex leaves), successive independent product-split of a
composite outcome, one-cut product-split, then rule 2 exchange of the
action for an observation. -/
noncomputable def identifiedPublishedCertificatePositive?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  match identifiedPublishedCertificate?
      (C := GraphModelClass.positive G) correct q with
  | some certificate => some certificate
  | none =>
      match chainSingletonIdentifiedPublishedCertificate? correct q with
      | some certificate => some certificate
      | none =>
          match consecutiveIdentifiedPublishedCertificate? correct q with
          | some certificate => some certificate
          | none =>
              match twoVertexIdentifiedPublishedCertificate? correct q with
              | some certificate => some certificate
              | none =>
                  match threeVertexIdentifiedPublishedCertificate? correct q with
                  | some certificate => some certificate
                  | none =>
                      match productSplitAllIdentifiedPublishedCertificate? correct q with
                      | some certificate => some certificate
                      | none =>
                          match productSplitIdentifiedPublishedCertificate? correct q with
                          | some certificate => some certificate
                          | none =>
                              exchangeActionIdentifiedPublishedCertificate? correct q

/-- Support tree of rule 3 shrinking `do(X)` to `do(X ∩ H)`.  Both
kernels are joints, so they are defined by cylinder evaluation. -/
noncomputable def shrinkActionRule3Derivation_supported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) (host : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome (NodeSet.diff q.action host)
        (NodeSet.inter q.action host))
    (model : FiniteLatentSCM S) (assignment : S.Assignment)
    (sourceSupported : q.sourceTerm.SupportedAt model assignment) :
    LocalDerivationSupport model assignment
      ((shrinkActionRule3Derivation (G := G) q host separated).compile
        correct) := by
  dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
    shrinkActionRule3Derivation]
  let nestedSource :=
    (q.shrinkAction host).supportedAt model assignment
  let hleft := JointKernelQuery.sourceTerm_eq_rule3Left_shrink q host
  let rule3LeftSupported :=
    ProbabilityTerm.SupportedAt.congr hleft sourceSupported
  let hright :=
    JointKernelQuery.shrinkAction_sourceTerm_eq_rule3Right q host
  let rule3RightSupported :=
    ProbabilityTerm.SupportedAt.congr hright nestedSource
  exact
    ⟨sourceSupported,
      ⟨nestedSource,
        ⟨rule3LeftSupported, ⟨rule3RightSupported, ()⟩⟩⟩⟩

/--
Rule 3 plus a nested published certificate of `P(Y | do(X ∩ H))`.
The identified formula is the nested formula: shrinking the
intervention does not change the observational expression ID returns
on the host.
-/
noncomputable def shrinkActionIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (host : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome (NodeSet.diff q.action host)
        (NodeSet.inter q.action host))
    (nested :
      PublishedJointCertificate C correct (q.shrinkAction host)) :
    PublishedJointCertificate C correct q where
  formula := nested.formula
  actionFree := nested.actionFree
  derivation :=
    shrinkActionIdentifiedIdDerivation q host separated nested.derivation
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      shrinkActionIdentifiedIdDerivation]
    let nestedSource :=
      (q.shrinkAction host).supportedAt model assignment
    let nestedSupported :=
      nested.supported model member assignment nestedSource
    exact
      ⟨sourceSupported,
        ⟨nestedSupported.endpoints.2,
          ⟨shrinkActionRule3Derivation_supported correct q host separated
            model assignment sourceSupported,
            nestedSupported⟩⟩⟩

/-- Boolean d-separation in `G_{\overline{X}}` plus a nested positive
certificate unpacks to the shrink-action wrapper.  The cut must be
nonempty so the nested query is strictly smaller. -/
noncomputable def shrinkActionIdentifiedPublishedCertificate?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) (host : NodeSet S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  if _hcut : NodeSet.isEmpty (NodeSet.diff q.action host) = false then
    if hsep : G.dSeparated (GraphMutilation.bar q.action) q.outcome
        (NodeSet.diff q.action host) (NodeSet.inter q.action host) =
          true then
      match identifiedPublishedCertificatePositive? correct
          (q.shrinkAction host) with
      | none => none
      | some nested =>
          some
            (shrinkActionIdentifiedPublishedCertificate correct q host
              (correct.pathDSeparated_of_dSeparated hsep) nested)
    else
      none
  else
    none

/-- Engine 4.3 host: the unique c-component of `G \ X` lifted to a
c-component of `G`, when `G` itself is not already a single
c-component.  Empty action or a 4.2 remaining is `none`. -/
def firstRestrictHost? (G : ObservedGraph S) (q : JointKernelQuery S) :
    Option (NodeSet S) :=
  if NodeSet.isEmpty q.action = true then
    none
  else
    match G.cComponents (NodeSet.diff NodeSet.full q.action) with
    | [component] =>
        if G.isSingleCComponent NodeSet.full = true then
          none
        else
          G.containingCComponent NodeSet.full component
    | _ => none

/-- Fuel-indexed nested 4.3 packer.  Each successful shrink consumes one
unit of fuel; the wrapper below starts with the action's member count,
which is enough because a nonempty cut strictly shortens `X ∩ H`. -/
noncomputable def identifiedPublishedCertificatePositiveWithShrinkFuel?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (fuel : Nat) (q : JointKernelQuery S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  match fuel with
  | 0 => identifiedPublishedCertificatePositive? correct q
  | n + 1 =>
      match identifiedPublishedCertificatePositive? correct q with
      | some certificate => some certificate
      | none =>
          match firstRestrictHost? G q with
          | none => none
          | some host =>
              if NodeSet.isEmpty (NodeSet.diff q.action host) = false then
                if hsep : G.dSeparated (GraphMutilation.bar q.action)
                    q.outcome (NodeSet.diff q.action host)
                    (NodeSet.inter q.action host) = true then
                  match identifiedPublishedCertificatePositiveWithShrinkFuel?
                      correct n (q.shrinkAction host) with
                  | none => none
                  | some nested =>
                      some
                        (shrinkActionIdentifiedPublishedCertificate correct q
                          host (correct.pathDSeparated_of_dSeparated hsep)
                          nested)
                else
                  none
              else
                none

/-- A core success is a fuel-indexed success at every remaining depth. -/
theorem identifiedPublishedCertificatePositiveWithShrinkFuel?_eq_some_of_core
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (fuel : Nat) (q : JointKernelQuery S)
    {cert :
      PublishedJointCertificate (GraphModelClass.positive G) correct q}
    (h : identifiedPublishedCertificatePositive? correct q = some cert) :
    identifiedPublishedCertificatePositiveWithShrinkFuel? correct fuel q =
      some cert := by
  cases fuel with
  | zero =>
      simpa [identifiedPublishedCertificatePositiveWithShrinkFuel?] using h
  | succ n =>
      simp [identifiedPublishedCertificatePositiveWithShrinkFuel?, h]

/-- Positive-class joint packer including nested 4.3 action shrink.
Fuel is the action's member count, matching the well-founded measure
`length_members_inter_lt_of_diff_nonempty`. -/
noncomputable def identifiedPublishedCertificatePositiveWithShrink?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S) :
    Option
      (PublishedJointCertificate (GraphModelClass.positive G) correct q) :=
  identifiedPublishedCertificatePositiveWithShrinkFuel? correct
    (NodeSet.members q.action).length q

theorem identifiedPublishedCertificatePositiveWithShrink?_eq_some_of_core
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    {cert :
      PublishedJointCertificate (GraphModelClass.positive G) correct q}
    (h : identifiedPublishedCertificatePositive? correct q = some cert) :
    identifiedPublishedCertificatePositiveWithShrink? correct q = some cert :=
  identifiedPublishedCertificatePositiveWithShrinkFuel?_eq_some_of_core
    correct _ q h

/--
Rule 1 with empty given-set: the side-condition graph is `G_{\overline{X}}`
with conditioner `X`.  Deleting `Z` from `P(Y | do(X), Z)` is therefore
the ordinary bar-graph d-separation of `Y` from `Z` given `X`.
-/
theorem pathDSeparated_rule1_empty_w
    (G : ObservedGraph S) (x y z : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar x) y z x) :
    PathSpecification.PathDSeparated G (GraphMutilation.bar x)
      y z (NodeSet.union x NodeSet.empty) := by
  simpa [NodeSet.union_empty_right] using separated

/--
Rule 1 deletes a nonempty conditioner once `Y` is path-d-separated from
`Z` given `X` in `G_{\overline{X}}`.  The right kernel is the joint
query `P(Y | do(X))`.
-/
def deleteConditionRule1Derivation {G : ObservedGraph S}
    (q : ConditionalKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome q.condition q.action) :
    PathDoCalculusDerivation G q.sourceTerm
      q.unconditionalJoint.sourceTerm :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (ConditionalKernelQuery.sourceTerm_eq_rule1Left_empty_w q)
    (ConditionalKernelQuery.unconditionalJoint_eq_rule1Right q)
    (DoCalculusDerivation.doRule
      (G := G) (separation := pathRuleSeparation G)
      (DoRuleApplication.rule1 (G := G) (separation := pathRuleSeparation G)
        q.action q.outcome q.condition NodeSet.empty
        (FourWayDisjoint.of_empty_w q.action q.outcome q.condition
          q.action_outcome_disjoint q.action_condition_disjoint
          q.outcome_condition_disjoint)
        (pathDSeparated_rule1_empty_w G q.action q.outcome q.condition
          separated)))

/-- Rule 1 followed by a joint identification of `P(Y | do(X))`. -/
def deleteConditionIdentifiedIdDerivation {G : ObservedGraph S}
    (q : ConditionalKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome q.condition q.action)
    {formula : ProbabilityTerm S}
    (joint :
      PathDoCalculusDerivation G q.unconditionalJoint.sourceTerm formula) :
    PathDoCalculusDerivation G q.sourceTerm formula :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (deleteConditionRule1Derivation q separated) joint

/--
Nonempty-condition identification when the query outcome is d-separated
from the conditioner given the action in `G_{\overline{X}}`.  The
formula is the joint identification of `P(Y | do(X))`.
-/
noncomputable def deleteConditionIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome q.condition q.action)
    (joint : PublishedJointCertificate C correct q.unconditionalJoint) :
    PublishedConditionalCertificate C correct q where
  formula := joint.formula
  actionFree := joint.actionFree
  derivation :=
    deleteConditionIdentifiedIdDerivation q separated joint.derivation
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      deleteConditionIdentifiedIdDerivation, deleteConditionRule1Derivation]
    let pYdo :=
      ProbabilityTerm.SupportedAt.congr
        (ConditionalKernelQuery.unconditionalJoint_eq_rule1Right q)
        (q.unconditionalJoint.supportedAt model assignment)
    let hleft := ConditionalKernelQuery.sourceTerm_eq_rule1Left_empty_w q
    let rule1LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    let inner :=
      joint.supported model member assignment
        (q.unconditionalJoint.supportedAt model assignment)
    exact
      ⟨sourceSupported,
        ⟨inner.endpoints.2,
          ⟨⟨sourceSupported,
              ⟨pYdo, ⟨rule1LeftSupported, ⟨pYdo, ()⟩⟩⟩⟩,
            inner⟩⟩⟩

/--
Rule 2 with empty given-set: the side-condition graph is
`G_{\overline{X}\underline{Z}}` with conditioner `X`.  Exchanging `Z`
from `P(Y | do(X), Z)` into `P(Y | do(X ∪ Z))` is therefore the
bar-underline d-separation of `Y` from `Z` given `X`.
-/
theorem pathDSeparated_rule2_empty_w
    (G : ObservedGraph S) (x y z : NodeSet S)
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline x z) y z x) :
    PathSpecification.PathDSeparated G
      (GraphMutilation.barUnderline x z) y z
      (NodeSet.union x NodeSet.empty) := by
  simpa [NodeSet.union_empty_right] using separated

/--
Rule 2 exchanges a nonempty conditioner for an intervention once `Y`
is path-d-separated from `Z` given `X` in `G_{\overline{X}\underline{Z}}`.
The left kernel is the joint query `P(Y | do(X ∪ Z))`.
-/
def exchangeConditionRule2Derivation {G : ObservedGraph S}
    (q : ConditionalKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline q.action q.condition)
        q.outcome q.condition q.action) :
    PathDoCalculusDerivation G q.sourceTerm
      q.intervenedCondition.sourceTerm :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    (ConditionalKernelQuery.sourceTerm_eq_rule2Right_empty_w q)
    (ConditionalKernelQuery.intervenedCondition_eq_rule2Left q)
    (DoCalculusDerivation.symm
      (G := G) (separation := pathRuleSeparation G)
      (DoCalculusDerivation.doRule
        (G := G) (separation := pathRuleSeparation G)
        (DoRuleApplication.rule2 (G := G) (separation := pathRuleSeparation G)
          q.action q.outcome q.condition NodeSet.empty
          (FourWayDisjoint.of_empty_w q.action q.outcome q.condition
            q.action_outcome_disjoint q.action_condition_disjoint
            q.outcome_condition_disjoint)
          (pathDSeparated_rule2_empty_w G q.action q.outcome q.condition
            separated))))

/-- Rule 2 followed by a joint identification of `P(Y | do(X ∪ Z))`. -/
def exchangeConditionIdentifiedIdDerivation {G : ObservedGraph S}
    (q : ConditionalKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline q.action q.condition)
        q.outcome q.condition q.action)
    {formula : ProbabilityTerm S}
    (joint :
      PathDoCalculusDerivation G q.intervenedCondition.sourceTerm formula) :
    PathDoCalculusDerivation G q.sourceTerm formula :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (exchangeConditionRule2Derivation q separated) joint

/--
Nonempty-condition identification when the query outcome is d-separated
from the conditioner given the action in `G_{\overline{X}\underline{Z}}`.
The formula is the joint identification of `P(Y | do(X ∪ Z))`.
-/
noncomputable def exchangeConditionIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G
        (GraphMutilation.barUnderline q.action q.condition)
        q.outcome q.condition q.action)
    (joint : PublishedJointCertificate C correct q.intervenedCondition) :
    PublishedConditionalCertificate C correct q where
  formula := joint.formula
  actionFree := joint.actionFree
  derivation :=
    exchangeConditionIdentifiedIdDerivation q separated joint.derivation
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      exchangeConditionIdentifiedIdDerivation, exchangeConditionRule2Derivation]
    let jointSourceSupported :=
      q.intervenedCondition.supportedAt model assignment
    let pLeft :=
      ProbabilityTerm.SupportedAt.congr
        (ConditionalKernelQuery.intervenedCondition_eq_rule2Left q)
        jointSourceSupported
    let pRight :=
      ProbabilityTerm.SupportedAt.congr
        (ConditionalKernelQuery.sourceTerm_eq_rule2Right_empty_w q)
        sourceSupported
    let inner :=
      joint.supported model member assignment jointSourceSupported
    exact
      ⟨sourceSupported,
        ⟨inner.endpoints.2,
          ⟨⟨sourceSupported,
              ⟨jointSourceSupported,
                ⟨pRight, ⟨pLeft, ⟨pLeft, ⟨pRight, ()⟩⟩⟩⟩⟩⟩,
            inner⟩⟩⟩

/-- Empty-condition IDC is the joint certificate, reindexed along
`P(Y | do(X), ∅) = P(Y | do(X))`. -/
noncomputable def publishedConditionalCertificate_of_empty_condition
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (emptyCondition : NodeSet.isEmpty q.condition = true)
    (joint : PublishedJointCertificate C correct
      (q.toJoint emptyCondition)) :
    PublishedConditionalCertificate C correct q where
  formula := joint.formula
  actionFree := joint.actionFree
  derivation :=
    DoCalculusDerivation.eqCongr
      (G := G) (separation := pathRuleSeparation G)
      (ConditionalKernelQuery.sourceTerm_eq_toJoint q emptyCondition)
      rfl
      joint.derivation
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
    let hsrc :=
      ConditionalKernelQuery.sourceTerm_eq_toJoint q emptyCondition
    let jointSupported :=
      ProbabilityTerm.SupportedAt.congr hsrc sourceSupported
    let inner :=
      joint.supported model member assignment jointSupported
    exact
      ⟨sourceSupported,
        ⟨inner.endpoints.2, inner⟩⟩

/--
A published conditional certificate when the conditioner is empty (the
joint packer), the action is empty (Bayes plus empty-action ID),
`Y ⊥ Z | X` in `G_{\overline{X}}` (rule 1 plus the joint packer), or
`Y ⊥ Z | X` in `G_{\overline{X}\underline{Z}}` (rule 2 plus the joint
packer of `P(Y | do(X ∪ Z))`).
-/
noncomputable def identifiedPublishedConditionalCertificate?
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S) :
    Option (PublishedConditionalCertificate C correct q) :=
  if hZ : NodeSet.isEmpty q.condition = true then
    match identifiedPublishedCertificate? (C := C) correct
        (q.toJoint hZ) with
    | none => none
    | some joint =>
        some (publishedConditionalCertificate_of_empty_condition correct q
          hZ joint)
  else if hact : NodeSet.isEmpty q.action = true then
    some (emptyActionIdentifiedPublishedConditionalCertificate correct q
      hact)
  else if hsep : G.dSeparated (GraphMutilation.bar q.action) q.outcome
      q.condition q.action = true then
    match identifiedPublishedCertificate? (C := C) correct
        q.unconditionalJoint with
    | none => none
    | some joint =>
        some (deleteConditionIdentifiedPublishedCertificate correct q
          (correct.pathDSeparated_of_dSeparated hsep) joint)
  else if hsep2 : G.dSeparated
      (GraphMutilation.barUnderline q.action q.condition) q.outcome
      q.condition q.action = true then
    match identifiedPublishedCertificate? (C := C) correct
        q.intervenedCondition with
    | none => none
    | some joint =>
        some (exchangeConditionIdentifiedPublishedCertificate correct q
          (correct.pathDSeparated_of_dSeparated hsep2) joint)
  else
    none

theorem identifiedPublishedConditionalCertificate?_isSome_of_empty_condition
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (hZ : NodeSet.isEmpty q.condition = true)
    (hjoint : (identifiedPublishedCertificate? (C := C) correct
        (q.toJoint hZ)).isSome = true) :
    (identifiedPublishedConditionalCertificate? (C := C) correct
        q).isSome = true := by
  dsimp [identifiedPublishedConditionalCertificate?]
  simp [hZ]
  revert hjoint
  cases identifiedPublishedCertificate? (C := C) correct (q.toJoint hZ) <;>
    simp

theorem identifiedPublishedConditionalCertificate?_isSome_of_empty_action
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (hact : NodeSet.isEmpty q.action = true) :
    (identifiedPublishedConditionalCertificate? (C := C) correct
        q).isSome = true := by
  dsimp [identifiedPublishedConditionalCertificate?]
  split
  · next hZ =>
      have hjoint :
          (identifiedPublishedCertificate? (C := C) correct
              (q.toJoint hZ)).isSome = true :=
        identifiedPublishedCertificate?_isSome_of_empty_action correct
          (q.toJoint hZ) hact
      revert hjoint
      cases identifiedPublishedCertificate? (C := C) correct
          (q.toJoint hZ) <;> simp
  · rfl

theorem identifiedPublishedConditionalCertificate?_isSome_of_delete_condition
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (hsep : G.dSeparated (GraphMutilation.bar q.action) q.outcome
      q.condition q.action = true)
    (hjoint : (identifiedPublishedCertificate? (C := C) correct
        q.unconditionalJoint).isSome = true) :
    (identifiedPublishedConditionalCertificate? (C := C) correct
        q).isSome = true := by
  by_cases hZ : NodeSet.isEmpty q.condition = true
  · exact identifiedPublishedConditionalCertificate?_isSome_of_empty_condition
      (C := C) correct q hZ hjoint
  · by_cases hact : NodeSet.isEmpty q.action = true
    · exact identifiedPublishedConditionalCertificate?_isSome_of_empty_action
        (C := C) correct q hact
    · simp [identifiedPublishedConditionalCertificate?, hZ, hact, hsep]
      revert hjoint
      cases identifiedPublishedCertificate? (C := C) correct
          q.unconditionalJoint <;> simp

theorem identifiedPublishedConditionalCertificate?_isSome_of_exchange_condition
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (hZ : ¬ (NodeSet.isEmpty q.condition = true))
    (hact : ¬ (NodeSet.isEmpty q.action = true))
    (hsep1 : ¬ (G.dSeparated (GraphMutilation.bar q.action) q.outcome
      q.condition q.action = true))
    (hsep : G.dSeparated
      (GraphMutilation.barUnderline q.action q.condition) q.outcome
      q.condition q.action = true)
    (hjoint : (identifiedPublishedCertificate? (C := C) correct
        q.intervenedCondition).isSome = true) :
    (identifiedPublishedConditionalCertificate? (C := C) correct
        q).isSome = true := by
  simp [identifiedPublishedConditionalCertificate?, hZ, hact, hsep1, hsep]
  revert hjoint
  cases identifiedPublishedCertificate? (C := C) correct
      q.intervenedCondition <;> simp


/-- Divide of two complementary observational marginals is defined in
every observationally positive model: the denominator is the cylinder
`P(Z)`. -/
noncomputable def complementaryMarginalDivide_supportedAt
    (model : FiniteLatentSCM S)
    (positive : ObservationallyPositive model)
    (numNodes denNodes : NodeSet S) (assignment : S.Assignment) :
    (ProbabilityTerm.divide
      (.marginalize (NodeSet.diff NodeSet.full numNodes)
        (observationalJointTerm S))
      (.marginalize (NodeSet.diff NodeSet.full denNodes)
        (observationalJointTerm S))).SupportedAt model assignment := by
  have hnum :=
    emptyActionKernel_equiv_fullMarginal model numNodes assignment
  have hden :=
    emptyActionKernel_equiv_fullMarginal model denNodes assignment
  have hpos : 0 <
      (((Kernel.mk denNodes NodeSet.empty NodeSet.empty).distribution
        model assignment).probVal
        (Kernel.agreesOn denNodes assignment)).num := by
    have hNoAction :
        (Kernel.mk denNodes NodeSet.empty NodeSet.empty).hasAction = false := by
      apply (finAny_eq_false_iff _).mpr
      intro _i
      rfl
    have hobs :
        (Kernel.mk denNodes NodeSet.empty NodeSet.empty).distribution
          model assignment = model.observationalDist := by
      simp [Kernel.distribution, hNoAction]
    simpa [hobs] using
      ObservationallyPositive.cylinder_positive positive denNodes assignment
  have hdenKernel :=
    Kernel.unconditionalDenote model denNodes NodeSet.empty assignment
  have hnumKernel :=
    Kernel.unconditionalDenote model numNodes NodeSet.empty assignment
  let numVal :=
    ((Kernel.mk numNodes NodeSet.empty NodeSet.empty).distribution
      model assignment).probVal (Kernel.agreesOn numNodes assignment)
  let denVal :=
    ((Kernel.mk denNodes NodeSet.empty NodeSet.empty).distribution
      model assignment).probVal (Kernel.agreesOn denNodes assignment)
  have hpos' : 0 < denVal.num := hpos
  have hdivKernels :
      ProbabilityResult.Equivalent
        ((ProbabilityTerm.divide
          (.kernel ⟨numNodes, NodeSet.empty, NodeSet.empty⟩)
          (.kernel ⟨denNodes, NodeSet.empty, NodeSet.empty⟩)).denote
          model assignment)
        (ProbabilityResult.divide (some numVal) (some denVal)) := by
    simpa [ProbabilityTerm.denote] using
      ProbabilityResult.divide_congr hnumKernel hdenKernel
  have hdivMargs :
      ProbabilityTerm.EquivalentAt model
        (.divide
          (.kernel ⟨numNodes, NodeSet.empty, NodeSet.empty⟩)
          (.kernel ⟨denNodes, NodeSet.empty, NodeSet.empty⟩))
        (.divide
          (.marginalize (NodeSet.diff NodeSet.full numNodes)
            (observationalJointTerm S))
          (.marginalize (NodeSet.diff NodeSet.full denNodes)
            (observationalJointTerm S)))
        assignment := by
    simpa [ProbabilityTerm.denote, observationalJointTerm] using
      ProbabilityResult.divide_congr hnum hden
  have hdefinedEq :
      ProbabilityResult.divide (some numVal) (some denVal) =
        some (QProb.div numVal denVal hpos') := by
    simp only [ProbabilityResult.divide]
    rw [dif_pos hpos']
  have kernelSupported :
      (ProbabilityTerm.divide
        (.kernel ⟨numNodes, NodeSet.empty, NodeSet.empty⟩)
        (.kernel ⟨denNodes, NodeSet.empty, NodeSet.empty⟩)).SupportedAt
        model assignment :=
    ⟨QProb.div numVal denVal hpos',
      ProbabilityResult.trans hdivKernels
        (by
          rw [hdefinedEq]
          exact ProbabilityResult.Equivalent.value (QProb.equiv_refl _))⟩
  exact ProbabilityTerm.SupportedAt.of_equivalent hdivMargs kernelSupported

/--
Bayes of two identified joints whose formulas are the complementary
observational marginals.  Denominator positivity uses the class's
observational cylinders, not denotational soundness of the joint
derivations.
-/
noncomputable def ofJointCertificates
    {G : ObservedGraph S} {C : GraphModelClass G}
    (obsPositive :
      forall {model : ExactModel S}, C.Mem model ->
        ObservationallyPositive model)
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (num : PublishedJointCertificate C correct q.jointNumerator)
    (den : PublishedJointCertificate C correct q.jointDenominator)
    (hnum :
      num.formula =
        .marginalize
          (NodeSet.diff NodeSet.full
            (NodeSet.union q.outcome q.condition))
          (observationalJointTerm S))
    (hden :
      den.formula =
        .marginalize (NodeSet.diff NodeSet.full q.condition)
          (observationalJointTerm S)) :
    PublishedConditionalCertificate C correct q where
  formula := .divide num.formula den.formula
  actionFree := ⟨num.actionFree, den.actionFree⟩
  derivation :=
    ofJointIdentifiedIdDerivation q num.derivation den.derivation
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      ofJointIdentifiedIdDerivation, conditionalBayesDerivation]
    let bayesDivide :=
      conditionalBayes_supportedAt model q assignment sourceSupported
    let divideKernels :=
      ProbabilityTerm.SupportedAt.congr
        (ConditionalKernelQuery.bayesDivide_eq_conditioningRight q)
        bayesDivide
    let formulaSupported :=
      ProbabilityTerm.SupportedAt.congr
        ((congrArg (fun n =>
            ProbabilityTerm.divide n
              (.marginalize (NodeSet.diff NodeSet.full q.condition)
                (observationalJointTerm S))) hnum.symm).trans
          (congrArg (ProbabilityTerm.divide num.formula) hden.symm))
        (complementaryMarginalDivide_supportedAt model (obsPositive member)
          (NodeSet.union q.outcome q.condition) q.condition assignment)
    let condLeft :=
      ProbabilityTerm.SupportedAt.congr
        (ConditionalKernelQuery.sourceTerm_eq_conditioningLeft_empty_w q)
        sourceSupported
    let innerNum :=
      num.supported model member assignment
        (q.jointNumerator.supportedAt model assignment)
    let innerDen :=
      den.supported model member assignment
        (q.jointDenominator.supportedAt model assignment)
    exact
      ⟨sourceSupported,
        ⟨formulaSupported,
          ⟨⟨sourceSupported,
              ⟨bayesDivide, ⟨condLeft, ⟨divideKernels, ()⟩⟩⟩⟩,
            ⟨bayesDivide,
              ⟨formulaSupported, ⟨innerNum, innerDen⟩⟩⟩⟩⟩⟩

/--
Bayes of two identified joints with arbitrary action-free formulas.
The outer divide is defined once the denominator formula's displayed
value is strictly positive; that hypothesis is discharged by cylinders
for complementary marginals and by factorwise observational kernels for
successive product-split, without importing denotational soundness.
-/
noncomputable def ofJointCertificatesFrom
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (num : PublishedJointCertificate C correct q.jointNumerator)
    (den : PublishedJointCertificate C correct q.jointDenominator)
    (hpos :
      forall (model : ExactModel S) (member : C.Mem model)
        (assignment : S.Assignment),
        0 <
          ((den.supported model member assignment
              (q.jointDenominator.supportedAt model assignment)).endpoints.2).1.num) :
    PublishedConditionalCertificate C correct q where
  formula := .divide num.formula den.formula
  actionFree := ⟨num.actionFree, den.actionFree⟩
  derivation :=
    ofJointIdentifiedIdDerivation q num.derivation den.derivation
  supported := fun model member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      ofJointIdentifiedIdDerivation, conditionalBayesDerivation]
    let bayesDivide :=
      conditionalBayes_supportedAt model q assignment sourceSupported
    let divideKernels :=
      ProbabilityTerm.SupportedAt.congr
        (ConditionalKernelQuery.bayesDivide_eq_conditioningRight q)
        bayesDivide
    let innerNum :=
      num.supported model member assignment
        (q.jointNumerator.supportedAt model assignment)
    let innerDen :=
      den.supported model member assignment
        (q.jointDenominator.supportedAt model assignment)
    let numFormulaSupported := innerNum.endpoints.2
    let denFormulaSupported := innerDen.endpoints.2
    let formulaSupported :=
      ProbabilityTerm.divide_supportedAt numFormulaSupported
        denFormulaSupported (hpos model member assignment)
    let condLeft :=
      ProbabilityTerm.SupportedAt.congr
        (ConditionalKernelQuery.sourceTerm_eq_conditioningLeft_empty_w q)
        sourceSupported
    exact
      ⟨sourceSupported,
        ⟨formulaSupported,
          ⟨⟨sourceSupported,
              ⟨bayesDivide, ⟨condLeft, ⟨divideKernels, ()⟩⟩⟩⟩,
            ⟨bayesDivide,
              ⟨formulaSupported, ⟨innerNum, innerDen⟩⟩⟩⟩⟩⟩

/-- Positive-class IDC: reuse the class-indexed packer, then Bayes of
two complementary-marginal joint certificates.  Complementary-marginal
formulas are the only Bayes denominators whose positivity is an
observational cylinder; consecutive 4.2 joints lift through
`identifiedPublishedConditionalCertificateFromPositiveJoint?`
instead. Successive product-split joints use
`ofPackedProductSplitAllCertificates?`. -/
noncomputable def ofPackedJointCertificates?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S) :
    Option
      (PublishedConditionalCertificate (GraphModelClass.positive G)
        correct q) :=
  match hnum : identifiedPublishedCertificate?
      (C := GraphModelClass.positive G) correct q.jointNumerator with
  | none => none
  | some num =>
      match hden : identifiedPublishedCertificate?
          (C := GraphModelClass.positive G) correct q.jointDenominator with
      | none => none
      | some den =>
          some
            (ofJointCertificates
              (fun {model} (member : (GraphModelClass.positive G).Mem model) =>
                member.2)
              correct q num den
              (identifiedPublishedCertificate?_formula correct
                q.jointNumerator hnum)
              (identifiedPublishedCertificate?_formula correct
                q.jointDenominator hden))

/-- Bayes of two successive product-split joints: the denominator
`∏_v P(v | X)` is strictly positive in every observationally positive
model. -/
noncomputable def ofPackedProductSplitAllCertificates?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S) :
    Option
      (PublishedConditionalCertificate (GraphModelClass.positive G)
        correct q) :=
  match productSplitAllIdentifiedPublishedCertificate? correct
      q.jointNumerator with
  | none => none
  | some num =>
      match hden : productSplitAllIdentifiedPublishedCertificate? correct
          q.jointDenominator with
      | none => none
      | some den =>
          some
            (ofJointCertificatesFrom correct q num den
              (fun model member assignment =>
                productSplitAllCertificate_formula_num_pos correct
                  q.jointDenominator den
                  (productSplitAllIdentifiedPublishedCertificate?_formula
                    correct q.jointDenominator hden)
                  model member assignment))

/-- An observational-kernel formula is strictly positive, so it can be
a Bayes denominator without complementary-marginal syntax. -/
theorem observationalKernelCertificate_formula_num_pos
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    (cert : PublishedJointCertificate (GraphModelClass.positive G) correct q)
    (outcome condition : NodeSet S)
    (hform : cert.formula =
      .kernel ⟨outcome, NodeSet.empty, condition⟩)
    (model : ExactModel S) (member : (GraphModelClass.positive G).Mem model)
    (assignment : S.Assignment) :
    0 <
      ((cert.supported model member assignment
          (q.supportedAt model assignment)).endpoints.2).1.num := by
  let denSup :=
    (cert.supported model member assignment
      (q.supportedAt model assignment)).endpoints.2
  let kerSup :=
    observationalConditional_supportedAt model member.2 outcome condition
      assignment
  let kerSup' := ProbabilityTerm.SupportedAt.congr hform.symm kerSup
  cases ProbabilityResult.trans (ProbabilityResult.symm denSup.2) kerSup'.2 with
  | value hequiv =>
      have hkerPos : 0 < kerSup'.1.num := by
        have hvals :
            ProbabilityResult.Equivalent (some kerSup'.1) (some kerSup.1) :=
          ProbabilityResult.trans (ProbabilityResult.symm kerSup'.2)
            (hform.symm ▸ kerSup.2)
        cases hvals with
        | value h =>
            exact
              (QProb.equiv_num_pos_iff h).mpr
                (observationalConditional_num_pos model member.2 outcome
                  condition assignment)
      exact (QProb.equiv_num_pos_iff hequiv).mpr hkerPos

/-- Bayes of two action-exchange joints: after rule 2 both formulas are
observational conditionals `P(Y, Z | X)` and `P(Z | X)`.  The
denominator is strictly positive by the conditioner-and-outcome
cylinder.  This covers singleton denominators that successive
product-split refuses. -/
noncomputable def ofPackedExchangeActionCertificates?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S) :
    Option
      (PublishedConditionalCertificate (GraphModelClass.positive G)
        correct q) :=
  match exchangeActionIdentifiedPublishedCertificate? correct
      q.jointNumerator with
  | none => none
  | some num =>
      match hden : exchangeActionIdentifiedPublishedCertificate? correct
          q.jointDenominator with
      | none => none
      | some den =>
          some
            (ofJointCertificatesFrom correct q num den
              (fun model member assignment =>
                observationalKernelCertificate_formula_num_pos correct
                  q.jointDenominator den q.condition q.action
                  (exchangeActionIdentifiedPublishedCertificate?_formula
                    correct q.jointDenominator hden)
                  model member assignment))

/--
Positive-class IDC wrapping the positive joint packer, including
nonempty 4.3 action shrink.  Empty conditioner is the joint query;
nonempty conditioner uses rule 1 in `G_{\overline{X}}` or rule 2 in
`G_{\overline{X}\underline{Z}}`.  The wrappers do not assume a
complementary-marginal formula, so consecutive 4.2, action-exchange,
and shrink-action joints lift as-is.
-/
noncomputable def identifiedPublishedConditionalCertificateFromPositiveJoint?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S) :
    Option
      (PublishedConditionalCertificate (GraphModelClass.positive G)
        correct q) :=
  if hZ : NodeSet.isEmpty q.condition = true then
    match identifiedPublishedCertificatePositiveWithShrink? correct
        (q.toJoint hZ) with
    | none => none
    | some joint =>
        some (publishedConditionalCertificate_of_empty_condition correct q
          hZ joint)
  else if hsep : G.dSeparated (GraphMutilation.bar q.action) q.outcome
      q.condition q.action = true then
    match identifiedPublishedCertificatePositiveWithShrink? correct
        q.unconditionalJoint with
    | none => none
    | some joint =>
        some (deleteConditionIdentifiedPublishedCertificate correct q
          (correct.pathDSeparated_of_dSeparated hsep) joint)
  else if hsep2 : G.dSeparated
      (GraphMutilation.barUnderline q.action q.condition) q.outcome
      q.condition q.action = true then
    match identifiedPublishedCertificatePositiveWithShrink? correct
        q.intervenedCondition with
    | none => none
    | some joint =>
        some (exchangeConditionIdentifiedPublishedCertificate correct q
          (correct.pathDSeparated_of_dSeparated hsep2) joint)
  else
    none

/--
Positive-class IDC packer: class-indexed complementary-marginal IDC,
then the positive joint packer (consecutive 4.2, singleton chain,
action-exchange) under empty conditioner / rule 1 / rule 2, then Bayes
of two successive product-split joints, then Bayes of two
complementary-marginal joints.
-/
noncomputable def identifiedPublishedConditionalCertificatePositive?
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S) :
    Option
      (PublishedConditionalCertificate (GraphModelClass.positive G)
        correct q) :=
  match identifiedPublishedConditionalCertificate?
      (C := GraphModelClass.positive G) correct q with
  | some certificate => some certificate
  | none =>
      match identifiedPublishedConditionalCertificateFromPositiveJoint?
          correct q with
      | some certificate => some certificate
      | none =>
      match ofPackedProductSplitAllCertificates? correct q with
      | some certificate => some certificate
      | none =>
          match ofPackedExchangeActionCertificates? correct q with
          | some certificate => some certificate
          | none => ofPackedJointCertificates? correct q

/-- Empty-condition IDC unpacks from the positive joint packer. -/
theorem identifiedPublishedConditionalCertificateFromPositiveJoint?_isSome_of_empty_condition
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (hZ : NodeSet.isEmpty q.condition = true)
    (hjoint :
      (identifiedPublishedCertificatePositive? correct
          (q.toJoint hZ)).isSome = true) :
    (identifiedPublishedConditionalCertificateFromPositiveJoint? correct
        q).isSome = true := by
  dsimp [identifiedPublishedConditionalCertificateFromPositiveJoint?]
  simp [hZ]
  revert hjoint
  cases hcore : identifiedPublishedCertificatePositive? correct
      (q.toJoint hZ) with
  | none => simp
  | some _ =>
      simp [identifiedPublishedCertificatePositiveWithShrink?_eq_some_of_core
        correct _ hcore]

/-- Rule 1 IDC unpacks from the positive joint packer of `P(Y | do(X))`. -/
theorem identifiedPublishedConditionalCertificateFromPositiveJoint?_isSome_of_delete_condition
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (hZ : ¬ (NodeSet.isEmpty q.condition = true))
    (hsep : G.dSeparated (GraphMutilation.bar q.action) q.outcome
      q.condition q.action = true)
    (hjoint :
      (identifiedPublishedCertificatePositive? correct
          q.unconditionalJoint).isSome = true) :
    (identifiedPublishedConditionalCertificateFromPositiveJoint? correct
        q).isSome = true := by
  simp [identifiedPublishedConditionalCertificateFromPositiveJoint?, hZ,
    hsep]
  revert hjoint
  cases hcore : identifiedPublishedCertificatePositive? correct
      q.unconditionalJoint with
  | none => simp
  | some _ =>
      simp [identifiedPublishedCertificatePositiveWithShrink?_eq_some_of_core
        correct _ hcore]

/-- Rule 2 IDC unpacks from the positive joint packer of
`P(Y | do(X ∪ Z))`. -/
theorem identifiedPublishedConditionalCertificateFromPositiveJoint?_isSome_of_exchange_condition
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (hZ : ¬ (NodeSet.isEmpty q.condition = true))
    (hsep1 : ¬ (G.dSeparated (GraphMutilation.bar q.action) q.outcome
      q.condition q.action = true))
    (hsep : G.dSeparated
      (GraphMutilation.barUnderline q.action q.condition) q.outcome
      q.condition q.action = true)
    (hjoint :
      (identifiedPublishedCertificatePositive? correct
          q.intervenedCondition).isSome = true) :
    (identifiedPublishedConditionalCertificateFromPositiveJoint? correct
        q).isSome = true := by
  simp [identifiedPublishedConditionalCertificateFromPositiveJoint?, hZ,
    hsep1, hsep]
  revert hjoint
  cases hcore : identifiedPublishedCertificatePositive? correct
      q.intervenedCondition with
  | none => simp
  | some _ =>
      simp [identifiedPublishedCertificatePositiveWithShrink?_eq_some_of_core
        correct _ hcore]

/-- The positive-class IDC packer succeeds whenever the positive joint
wrapper does. -/
theorem identifiedPublishedConditionalCertificatePositive?_isSome_of_positive_joint
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : ConditionalKernelQuery S)
    (hjoint :
      (identifiedPublishedConditionalCertificateFromPositiveJoint? correct
          q).isSome = true) :
    (identifiedPublishedConditionalCertificatePositive? correct
        q).isSome = true := by
  dsimp [identifiedPublishedConditionalCertificatePositive?]
  cases identifiedPublishedConditionalCertificate?
      (C := GraphModelClass.positive G) correct q with
  | some _ =>
      rfl
  | none =>
      revert hjoint
      cases identifiedPublishedConditionalCertificateFromPositiveJoint?
          correct q <;> simp

/-- Successful empty-action ID returns exactly the certificate formula. -/
theorem emptyActionIdentifiedTerm_eq_identifyJoint
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (emptyAction : NodeSet.isEmpty q.action = true)
    {term : ProbabilityTerm S}
    (h : Legacy.identifyJoint G q = IdentificationOutcome.identified term) :
    term =
      .marginalize (NodeSet.diff NodeSet.full q.outcome)
        (observationalJointTerm S) := by
  have hsucc := identifyJoint_empty_action_succeeds G q emptyAction
  rw [hsucc] at h
  injection h with hterm
  exact hterm.symm

/--
No free c-component of `G \ X` means `V \ X` is empty.  The query
outcome is disjoint from the action, so `Y` is empty.
-/
theorem outcome_isEmpty_of_empty_free
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (hfc : G.cComponents (NodeSet.diff NodeSet.full q.action) = []) :
    NodeSet.isEmpty q.outcome = true := by
  refine (NodeSet.isEmpty_eq_true_iff q.outcome).mpr fun i => ?_
  cases hy : q.outcome i with
  | false =>
      rfl
  | true =>
      have hact : q.action i = false :=
        q.outcome_action_disjoint i hy
      have hdiff :
          NodeSet.diff NodeSet.full q.action i = true := by
        simp [NodeSet.diff, NodeSet.full, hact]
      rcases cComponents_covers G (NodeSet.diff NodeSet.full q.action)
          hdiff with ⟨_component, hmem, _hi⟩
      simp [hfc] at hmem

/--
No free c-component of `G \ X` means `V ⊆ X`.  ID returns the
observational joint marginalized off every vertex.
-/
theorem identifyJoint_eq_identified_of_empty_free
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc : G.cComponents (NodeSet.diff NodeSet.full q.action) = []) :
    Legacy.identifyJoint G q =
      IdentificationOutcome.identified
        (.marginalize NodeSet.full (observationalJointTerm S)) := by
  have hinter : NodeSet.inter q.action NodeSet.full = q.action :=
    NodeSet.inter_full_right _
  have hy : NodeSet.inter q.outcome NodeSet.full = q.outcome :=
    NodeSet.inter_full_right _
  have hex' :
      NodeSet.isEmpty (NodeSet.inter q.action NodeSet.full) = false := by
    simpa [hinter] using hex
  have hkept' :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.inter q.action NodeSet.full))
          (NodeSet.inter q.outcome NodeSet.full))
        NodeSet.full = true := by
    simpa [hinter, hy] using hkept
  have hfc' :
      G.cComponents
        (NodeSet.diff NodeSet.full (NodeSet.inter q.action NodeSet.full)) =
        [] := by
    simpa [hinter] using hfc
  rw [Legacy.identifyJoint, identificationFuel]
  simpa [hinter, hy] using
    identifyFuel_eq_identified_of_empty_free
      (S.count * Nat.succ S.count * Nat.succ S.count) G NodeSet.full
      q.outcome q.action (observationalJointTerm S) hex' hkept' hfc'

/--
A first ancestral restriction whose nested remaining set misses `X` is
empty-action ID on that ancestral set.  The cubic fuel budget supplies
the two units this takes once the action is nonempty, hence `|V| > 0`.
-/
theorem identifyJoint_eq_identified_of_first_shrink_empty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = false)
    (hexNested :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)) = true) :
    Legacy.identifyJoint G q =
      IdentificationOutcome.identified
        (.marginalize
          (NodeSet.diff
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)
            (NodeSet.inter q.outcome
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome)))
          (.marginalize
            (NodeSet.diff NodeSet.full
              (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
                q.outcome))
            (observationalJointTerm S))) := by
  have hinter : NodeSet.inter q.action NodeSet.full = q.action :=
    NodeSet.inter_full_right _
  have hy : NodeSet.inter q.outcome NodeSet.full = q.outcome :=
    NodeSet.inter_full_right _
  have hex' :
      NodeSet.isEmpty (NodeSet.inter q.action NodeSet.full) = false := by
    simpa [hinter] using hex
  have hkept' :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.inter q.action NodeSet.full))
          (NodeSet.inter q.outcome NodeSet.full))
        NodeSet.full = false := by
    simpa [hinter, hy] using hkept
  have hexNested' :
      NodeSet.isEmpty
        (NodeSet.inter q.action
          (G.ancestralSet NodeSet.full
            (GraphMutilation.bar (NodeSet.inter q.action NodeSet.full))
            (NodeSet.inter q.outcome NodeSet.full))) = true := by
    simpa [hinter, hy] using hexNested
  rcases (NodeSet.isEmpty_eq_false_iff q.action).mp hex with ⟨i, _hi⟩
  have hcount : 0 < S.count := Nat.zero_lt_of_lt i.isLt
  have hpos :
      0 < S.count * Nat.succ S.count * Nat.succ S.count :=
    Nat.mul_pos (Nat.mul_pos hcount (Nat.succ_pos _)) (Nat.succ_pos _)
  have hn :
      S.count * Nat.succ S.count * Nat.succ S.count =
        Nat.succ (Nat.pred (S.count * Nat.succ S.count * Nat.succ S.count)) :=
    (Nat.succ_pred_eq_of_pos hpos).symm
  rw [Legacy.identifyJoint, identificationFuel, hn]
  simpa [hinter, hy] using
    identifyFuel_eq_identified_of_shrink_empty
      (Nat.pred (S.count * Nat.succ S.count * Nat.succ S.count)) G
      NodeSet.full q.outcome q.action (observationalJointTerm S)
      hex' hkept' hexNested'

/--
Every outcome vertex is ancestral of itself in `G_{\overline{X}}`, so
`Y ⊆ An(Y)_{G_{\overline{X}}}`.
-/
theorem outcome_subset_ancestralSet
    (G : ObservedGraph S) (q : JointKernelQuery S) :
    NodeSet.Subset q.outcome
      (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
        q.outcome) := by
  intro i hi
  exact ancestralSet_contains_targets G NodeSet.full
    (GraphMutilation.bar q.action) q.outcome rfl hi

/--
The two ID nested-marginal blocks on `An(Y)_{G_{\overline{X}}}` cover
the empty-action complementary set `V \ Y`.
-/
theorem first_shrink_empty_summed_eq
    (G : ObservedGraph S) (q : JointKernelQuery S) :
    NodeSet.union
      (NodeSet.diff
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        (NodeSet.inter q.outcome
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)))
      (NodeSet.diff NodeSet.full
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)) =
      NodeSet.diff NodeSet.full q.outcome := by
  have hY := outcome_subset_ancestralSet G q
  have hinter :
      NodeSet.inter q.outcome
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome) =
        q.outcome := by
    rw [NodeSet.inter_comm]
    exact NodeSet.inter_eq_of_subset hY
  rw [hinter]
  exact NodeSet.union_diff_of_subset hY

/-- `Y ∩ An(Y) = Y` in `G_{\overline{X}}`. -/
theorem outcome_inter_ancestralSet
    (G : ObservedGraph S) (q : JointKernelQuery S) :
    NodeSet.inter q.outcome
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome) =
      q.outcome := by
  rw [NodeSet.inter_comm]
  exact NodeSet.inter_eq_of_subset (outcome_subset_ancestralSet G q)

/--
Empty-action marginalization from `P(Y)` onto the ancestral host `A`,
writing `∑_{A \ Y} P(A)` once `Y ⊆ A`.
-/
theorem ancestralSliceMarginalizationTerm_eq
    (A Y : NodeSet S) (hY : NodeSet.Subset Y A) :
    ProbabilityTerm.marginalize (NodeSet.diff A Y)
      (.kernel ⟨NodeSet.union Y (NodeSet.diff A Y),
        NodeSet.empty, NodeSet.empty⟩) =
      ProbabilityTerm.marginalize (NodeSet.diff A Y)
        (.kernel ⟨A, NodeSet.empty, NodeSet.empty⟩) := by
  rw [NodeSet.union_diff_eq hY]

def ancestralSliceIdDerivation {G : ObservedGraph S}
    (A Y : NodeSet S) (hY : NodeSet.Subset Y A) :
    PathDoCalculusDerivation G
      (.kernel ⟨Y, NodeSet.empty, NodeSet.empty⟩)
      (.marginalize (NodeSet.diff A Y)
        (.kernel ⟨A, NodeSet.empty, NodeSet.empty⟩)) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    rfl
    (ancestralSliceMarginalizationTerm_eq A Y hY).symm
    (DoCalculusDerivation.marginalization
      (G := G) (separation := pathRuleSeparation G)
      NodeSet.empty Y (NodeSet.diff A Y) NodeSet.empty
      (FourWayDisjoint.emptyActionConditioning Y (NodeSet.diff A Y)
        (NodeSet.Disjoint.diff_left A Y)))

/--
Two empty-action marginalizations: `P(Y) = ∑_{A \ Y} ∑_{V \ A} P(V)`
when `Y ⊆ A`.
-/
def nestedEmptyActionIdDerivation {G : ObservedGraph S}
    (A Y : NodeSet S) (hY : NodeSet.Subset Y A) :
    PathDoCalculusDerivation G
      (.kernel ⟨Y, NodeSet.empty, NodeSet.empty⟩)
      (.marginalize (NodeSet.diff A Y)
        (.marginalize (NodeSet.diff NodeSet.full A)
          (observationalJointTerm S))) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (ancestralSliceIdDerivation (G := G) A Y hY)
    (DoCalculusDerivation.marginalizeCongr
      (G := G) (separation := pathRuleSeparation G)
      (NodeSet.diff A Y)
      (unconditionalEmptyActionIdDerivation (G := G) A))

/-- The nested ancestral formula matches the first-shrink-empty ID output. -/
theorem first_shrink_empty_nested_eq
    (G : ObservedGraph S) (q : JointKernelQuery S) :
    ProbabilityTerm.marginalize
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          q.outcome)
        (.marginalize
          (NodeSet.diff NodeSet.full
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          (observationalJointTerm S)) =
      ProbabilityTerm.marginalize
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (.marginalize
          (NodeSet.diff NodeSet.full
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          (observationalJointTerm S)) := by
  rw [outcome_inter_ancestralSet G q]

def firstShrinkEmptyNestedIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S) :
    PathDoCalculusDerivation G
      (.kernel ⟨q.outcome, NodeSet.empty, NodeSet.empty⟩)
      (.marginalize
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (.marginalize
          (NodeSet.diff NodeSet.full
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          (observationalJointTerm S))) :=
  DoCalculusDerivation.eqCongr
    (G := G) (separation := pathRuleSeparation G)
    rfl
    (first_shrink_empty_nested_eq G q).symm
    (nestedEmptyActionIdDerivation (G := G)
      (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome)
      q.outcome (outcome_subset_ancestralSet G q))

/--
Rule 3 deletes the action, then two empty-action marginalizations write
the first-shrink-empty ID formula.
-/
def firstShrinkEmptyIdentifiedIdDerivation {G : ObservedGraph S}
    (q : JointKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome q.action NodeSet.empty) :
    PathDoCalculusDerivation G q.sourceTerm
      (.marginalize
        (NodeSet.diff
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)
          (NodeSet.inter q.outcome
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome)))
        (.marginalize
          (NodeSet.diff NodeSet.full
            (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
              q.outcome))
          (observationalJointTerm S))) :=
  DoCalculusDerivation.trans
    (G := G) (separation := pathRuleSeparation G)
    (deleteActionRule3Derivation q separated)
    (firstShrinkEmptyNestedIdDerivation q)

/-- Support tree of `P(Y) = ∑_{A \ Y} P(A)` under `Y ⊆ A`. -/
noncomputable def ancestralSliceIdDerivation_supported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (A Y : NodeSet S) (hY : NodeSet.Subset Y A)
    (model : FiniteLatentSCM S) (assignment : S.Assignment) :
    LocalDerivationSupport model assignment
      ((ancestralSliceIdDerivation (G := G) A Y hY).compile correct) :=
  let pY := emptyActionKernel_supportedAt model Y assignment
  let slice := ancestralSliceMarginal_supportedAt model A Y assignment
  let innerRight :=
    ProbabilityTerm.SupportedAt.congr
      (ancestralSliceMarginalizationTerm_eq A Y hY).symm slice
  ⟨pY, ⟨slice, ⟨pY, ⟨innerRight, ()⟩⟩⟩⟩

/-- Support of summing a family of empty-action IDs over `A \ Y`. -/
noncomputable def nestedMarginalizeCongr_supported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (A Y : NodeSet S)
    (model : FiniteLatentSCM S) (assignment : S.Assignment) :
    LocalDerivationSupport model assignment
      (PathDoCalculusDerivation.compile correct
        (DoCalculusDerivation.marginalizeCongr
          (G := G) (separation := pathRuleSeparation G)
          (NodeSet.diff A Y)
          (unconditionalEmptyActionIdDerivation (G := G) A))) := by
  dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules]
  exact
    ⟨ancestralSliceMarginal_supportedAt model A Y assignment,
      ⟨nestedAncestralMarginal_supportedAt model A Y assignment,
        fun variant _ =>
          unconditionalEmptyActionIdDerivation_supported correct A
            model variant⟩⟩

/-- Support tree of `P(Y) = ∑_{A \ Y} ∑_{V \ A} P(V)` under `Y ⊆ A`. -/
noncomputable def nestedEmptyActionIdDerivation_supported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (A Y : NodeSet S) (hY : NodeSet.Subset Y A)
    (model : FiniteLatentSCM S) (assignment : S.Assignment) :
    LocalDerivationSupport model assignment
      ((nestedEmptyActionIdDerivation (G := G) A Y hY).compile correct) := by
  dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
    nestedEmptyActionIdDerivation]
  exact
    ⟨emptyActionKernel_supportedAt model Y assignment,
      ⟨nestedAncestralMarginal_supportedAt model A Y assignment,
        ⟨ancestralSliceIdDerivation_supported correct A Y hY model assignment,
          nestedMarginalizeCongr_supported correct A Y model assignment⟩⟩⟩

/-- Support tree of empty-action nested ID onto the first-shrink-empty
formula, which writes `A \ (Y ∩ A)` in place of `A \ Y`. -/
noncomputable def firstShrinkEmptyNestedIdDerivation_supported
    {G : ObservedGraph S} (correct : DSeparationCorrectness G)
    (q : JointKernelQuery S)
    (model : FiniteLatentSCM S) (assignment : S.Assignment) :
    LocalDerivationSupport model assignment
      ((firstShrinkEmptyNestedIdDerivation (G := G) q).compile correct) := by
  dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
    firstShrinkEmptyNestedIdDerivation]
  let A :=
    G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
  let nested :=
    nestedAncestralMarginal_supportedAt model A q.outcome assignment
  let identified :=
    ProbabilityTerm.SupportedAt.congr
      (first_shrink_empty_nested_eq G q) nested
  exact
    ⟨emptyActionKernel_supportedAt model q.outcome assignment,
      ⟨identified,
        nestedEmptyActionIdDerivation_supported correct A q.outcome
          (outcome_subset_ancestralSet G q) model assignment⟩⟩

/--
When `Y ⊥ X` in `G_{\overline{X}}`, the first-shrink-empty ID formula
is a published certificate: rule 3 deletes the action, then two
empty-action marginalizations write `∑_{An(Y) \ Y} ∑_{V \ An(Y)} P(V)`.
The engine returns this same term on the first-shrink-empty branch
(`identifyJoint_eq_identified_of_first_shrink_empty`).
-/
noncomputable def firstShrinkEmptyIdentifiedPublishedCertificate
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S)
    (separated :
      PathSpecification.PathDSeparated G (GraphMutilation.bar q.action)
        q.outcome q.action NodeSet.empty) :
    PublishedJointCertificate C correct q where
  formula :=
    .marginalize
      (NodeSet.diff
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        (NodeSet.inter q.outcome
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome)))
      (.marginalize
        (NodeSet.diff NodeSet.full
          (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
            q.outcome))
        (observationalJointTerm S))
  actionFree := observationalJointTerm_actionFree S
  derivation := firstShrinkEmptyIdentifiedIdDerivation q separated
  supported := fun model _member assignment sourceSupported => by
    dsimp [PathDoCalculusDerivation.compile, DoCalculusDerivation.mapRules,
      firstShrinkEmptyIdentifiedIdDerivation, deleteActionRule3Derivation]
    let pY :=
      emptyActionKernel_supportedAt model q.outcome assignment
    let A :=
      G.ancestralSet NodeSet.full (GraphMutilation.bar q.action) q.outcome
    let nested :=
      nestedAncestralMarginal_supportedAt model A q.outcome assignment
    let formulaSupported :=
      ProbabilityTerm.SupportedAt.congr
        (first_shrink_empty_nested_eq G q) nested
    let hleft := JointKernelQuery.sourceTerm_eq_rule3Left_empty_xw q
    let rule3LeftSupported :=
      ProbabilityTerm.SupportedAt.congr hleft sourceSupported
    exact
      ⟨sourceSupported,
        ⟨formulaSupported,
          ⟨⟨sourceSupported,
              ⟨pY, ⟨rule3LeftSupported, ⟨pY, ()⟩⟩⟩⟩,
            firstShrinkEmptyNestedIdDerivation_supported correct q
              model assignment⟩⟩⟩

/-- Boolean d-separation unpacks to the first-shrink-empty nested
certificate. -/
noncomputable def firstShrinkEmptyIdentifiedPublishedCertificate?
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S) :
    Option (PublishedJointCertificate C correct q) :=
  if h : G.dSeparated (GraphMutilation.bar q.action) q.outcome q.action
      NodeSet.empty = true then
    some (firstShrinkEmptyIdentifiedPublishedCertificate correct q
      (correct.pathDSeparated_of_dSeparated h))
  else
    none

theorem firstShrinkEmptyIdentifiedPublishedCertificate?_isSome_iff
    {G : ObservedGraph S} {C : GraphModelClass G}
    (correct : DSeparationCorrectness G) (q : JointKernelQuery S) :
    (firstShrinkEmptyIdentifiedPublishedCertificate? (C := C) correct
        q).isSome =
      G.dSeparated (GraphMutilation.bar q.action) q.outcome q.action
        NodeSet.empty := by
  dsimp [firstShrinkEmptyIdentifiedPublishedCertificate?]
  split
  · next h => exact h.symm
  · next h =>
      cases hb :
          G.dSeparated (GraphMutilation.bar q.action) q.outcome q.action
            NodeSet.empty with
      | true => exact False.elim (h hb)
      | false => rfl

/--
Top-level 4.2: the unique free c-component of `G \ X` is already a
c-component of `G`, so ID returns the chain-rule factorization of that
component, marginalized to `Y`.
-/
theorem identifyJoint_eq_identified_of_chain
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {component : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [component])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun piece => NodeSet.equal piece component) = true) :
    Legacy.identifyJoint G q =
      IdentificationOutcome.identified
        (.marginalize (NodeSet.diff component q.outcome)
          (chainProduct NodeSet.full component)) := by
  have hinter : NodeSet.inter q.action NodeSet.full = q.action :=
    NodeSet.inter_full_right _
  have hy : NodeSet.inter q.outcome NodeSet.full = q.outcome :=
    NodeSet.inter_full_right _
  have hex' :
      NodeSet.isEmpty (NodeSet.inter q.action NodeSet.full) = false := by
    simpa [hinter] using hex
  have hkept' :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.inter q.action NodeSet.full))
          (NodeSet.inter q.outcome NodeSet.full))
        NodeSet.full = true := by
    simpa [hinter, hy] using hkept
  have hfc' :
      G.cComponents
        (NodeSet.diff NodeSet.full (NodeSet.inter q.action NodeSet.full)) =
        [component] := by
    simpa [hinter] using hfc
  rw [Legacy.identifyJoint, identificationFuel]
  simpa [hinter, hy] using
    identifyFuel_eq_identified_of_chain
      (S.count * Nat.succ S.count * Nat.succ S.count) G NodeSet.full
      q.outcome q.action (observationalJointTerm S) hex' hkept' hfc'
      hsingle hany

/--
Top-level 4.2 whose unique free c-component is the outcome itself: the
engine formula is the complementary sum `∑_{Y \ Y} Q[Y]`, which is the
formula of `chainSingletonIdentifiedPublishedCertificate` once `Y` is
a singleton whose topological predecessors are the action.
-/
theorem identifyJoint_eq_identified_of_chain_outcome
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [q.outcome])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun piece => NodeSet.equal piece q.outcome) = true) :
    Legacy.identifyJoint G q =
      IdentificationOutcome.identified
        (.marginalize (NodeSet.diff q.outcome q.outcome)
          (chainProduct NodeSet.full q.outcome)) :=
  identifyJoint_eq_identified_of_chain G q hex hkept hfc hsingle hany

/--
A first 4.3 restriction unpacks as the nested ID run on the containing
c-component, with action `X ∩ larger` and the chain-rule joint on that
host.  Dual of `identifyJoint_eq_failed_of_first_restrict`.
-/
theorem identifyJoint_eq_identified_of_first_restrict
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {term : ProbabilityTerm S} {component larger : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [component])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent NodeSet.full component = some larger)
    (h : Legacy.identifyJoint G q = IdentificationOutcome.identified term) :
    Legacy.identifyFuel
        (S.count * Nat.succ S.count * Nat.succ S.count) G larger
        q.outcome (NodeSet.inter q.action larger)
        (chainProduct NodeSet.full larger) =
      IdentificationOutcome.identified term := by
  have hinter : NodeSet.inter q.action NodeSet.full = q.action :=
    NodeSet.inter_full_right _
  have hy : NodeSet.inter q.outcome NodeSet.full = q.outcome :=
    NodeSet.inter_full_right _
  have hex' :
      NodeSet.isEmpty (NodeSet.inter q.action NodeSet.full) = false := by
    simpa [hinter] using hex
  have hkept' :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.inter q.action NodeSet.full))
          (NodeSet.inter q.outcome NodeSet.full))
        NodeSet.full = true := by
    simpa [hinter, hy] using hkept
  have hfc' :
      G.cComponents
        (NodeSet.diff NodeSet.full (NodeSet.inter q.action NodeSet.full)) =
        [component] := by
    simpa [hinter] using hfc
  have hfuel :
      Legacy.identifyFuel (identificationFuel S) G NodeSet.full q.outcome
        q.action (observationalJointTerm S) =
        IdentificationOutcome.identified term := h
  rw [identificationFuel] at hfuel
  have hnested :=
    identifyFuel_eq_identified_of_restrict
      (S.count * Nat.succ S.count * Nat.succ S.count) G NodeSet.full
      q.outcome q.action (observationalJointTerm S) hex' hkept' hfc'
      hsingle hany hcont hfuel
  simpa [hinter] using hnested

/--
A first 4.3 restriction whose nested host misses `X` is empty-action ID
on that host, returning a marginal of the chain-rule joint `Q[S']`.
-/
theorem identifyJoint_eq_identified_of_first_restrict_empty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {component larger : NodeSet S}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) = [component])
    (hsingle : G.isSingleCComponent NodeSet.full = false)
    (hany :
      (G.cComponents NodeSet.full).any
        (fun piece => NodeSet.equal piece component) = false)
    (hcont :
      G.containingCComponent NodeSet.full component = some larger)
    (hexNested : NodeSet.isEmpty (NodeSet.inter q.action larger) = true) :
    Legacy.identifyJoint G q =
      IdentificationOutcome.identified
        (.marginalize
          (NodeSet.diff larger (NodeSet.inter q.outcome larger))
          (chainProduct NodeSet.full larger)) := by
  have hinter : NodeSet.inter q.action NodeSet.full = q.action :=
    NodeSet.inter_full_right _
  have hy : NodeSet.inter q.outcome NodeSet.full = q.outcome :=
    NodeSet.inter_full_right _
  have hex' :
      NodeSet.isEmpty (NodeSet.inter q.action NodeSet.full) = false := by
    simpa [hinter] using hex
  have hkept' :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.inter q.action NodeSet.full))
          (NodeSet.inter q.outcome NodeSet.full))
        NodeSet.full = true := by
    simpa [hinter, hy] using hkept
  have hfc' :
      G.cComponents
        (NodeSet.diff NodeSet.full (NodeSet.inter q.action NodeSet.full)) =
        [component] := by
    simpa [hinter] using hfc
  have hexNested' :
      NodeSet.isEmpty
        (NodeSet.inter (NodeSet.inter q.action NodeSet.full) larger) =
          true := by
    simpa [hinter] using hexNested
  rcases (NodeSet.isEmpty_eq_false_iff q.action).mp hex with ⟨i, _hi⟩
  have hcount : 0 < S.count := Nat.zero_lt_of_lt i.isLt
  have hpos :
      0 < S.count * Nat.succ S.count * Nat.succ S.count :=
    Nat.mul_pos (Nat.mul_pos hcount (Nat.succ_pos _)) (Nat.succ_pos _)
  have hn :
      S.count * Nat.succ S.count * Nat.succ S.count =
        Nat.succ (Nat.pred (S.count * Nat.succ S.count * Nat.succ S.count)) :=
    (Nat.succ_pred_eq_of_pos hpos).symm
  rw [Legacy.identifyJoint, identificationFuel, hn]
  simpa [hinter, hy] using
    identifyFuel_eq_identified_of_restrict_empty
      (Nat.pred (S.count * Nat.succ S.count * Nat.succ S.count)) G
      NodeSet.full q.outcome q.action (observationalJointTerm S)
      hex' hkept' hfc' hsingle hany hcont hexNested'

/--
A first product split unpacks as identified runs on the listed free
c-components, assembled by `productTerms` and marginalized off `V \ (Y ∪ X)`.
Dual of `identifyJoint_eq_failed_of_first_product`.
-/
theorem identifyJoint_eq_identified_of_first_product
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {term : ProbabilityTerm S}
    {component component2 : NodeSet S} {rest : List (NodeSet S)}
    (hex : NodeSet.isEmpty q.action = false)
    (hkept :
      NodeSet.equal
        (G.ancestralSet NodeSet.full (GraphMutilation.bar q.action)
          q.outcome)
        NodeSet.full = true)
    (hfc :
      G.cComponents (NodeSet.diff NodeSet.full q.action) =
        component :: component2 :: rest)
    (h : Legacy.identifyJoint G q = IdentificationOutcome.identified term) :
    Exists fun terms =>
      term =
          ProbabilityTerm.marginalize
            (NodeSet.diff NodeSet.full
              (NodeSet.union q.outcome q.action))
            (productTerms terms) ∧
        (component :: component2 :: rest).map (fun piece =>
            Legacy.identifyFuel
              (S.count * Nat.succ S.count * Nat.succ S.count) G
              NodeSet.full piece (NodeSet.diff NodeSet.full piece)
              (observationalJointTerm S)) =
          terms.map IdentificationOutcome.identified := by
  have hinter : NodeSet.inter q.action NodeSet.full = q.action :=
    NodeSet.inter_full_right _
  have hy : NodeSet.inter q.outcome NodeSet.full = q.outcome :=
    NodeSet.inter_full_right _
  have hex' :
      NodeSet.isEmpty (NodeSet.inter q.action NodeSet.full) = false := by
    simpa [hinter] using hex
  have hkept' :
      NodeSet.equal
        (G.ancestralSet NodeSet.full
          (GraphMutilation.bar (NodeSet.inter q.action NodeSet.full))
          (NodeSet.inter q.outcome NodeSet.full))
        NodeSet.full = true := by
    simpa [hinter, hy] using hkept
  have hfc' :
      G.cComponents
        (NodeSet.diff NodeSet.full (NodeSet.inter q.action NodeSet.full)) =
        component :: component2 :: rest := by
    simpa [hinter] using hfc
  have hfuel :
      Legacy.identifyFuel (identificationFuel S) G NodeSet.full q.outcome
        q.action (observationalJointTerm S) =
        IdentificationOutcome.identified term := h
  rw [identificationFuel] at hfuel
  rcases identifyFuel_eq_identified_of_product
      (S.count * Nat.succ S.count * Nat.succ S.count) G NodeSet.full
      q.outcome q.action (observationalJointTerm S) hex' hkept' hfc'
      hfuel with ⟨terms, hterm, hmap⟩
  refine ⟨terms, ?_, hmap⟩
  simpa [hinter, hy] using hterm

/-! The shared connectivity, containing-component and rank lemmas
now live in Causality.ComponentConnectivity and
Causality.IdentificationRank, imported above. The forest constructors
and historical trace proofs below keep their established public API. -/


namespace IdentificationUnfinishedTrace

/--
Every structurally unfinished ID run ends by exhausting fuel.  The other
syntactic terminal, a missing containing c-component, contradicts the
constructive host-containment theorem.  Thus the remaining totality task is
precisely the advertised recursion-depth bound; there is no independent
partition-shape gap hidden behind the same sentinel.
-/
theorem endsInExhaustion_eq_true
    {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S}
    (trace :
      IdentificationUnfinishedTrace G fuel remaining outcome action current) :
    trace.endsInExhaustion = true := by
  induction trace with
  | exhausted =>
      rfl
  | missingHost _fuel remaining _outcome action _current component
      _actionNonempty _ancestral oneFreeComponent
      _severalRemainingComponents _componentNotMaximal noContainingComponent =>
      exact False.elim
        (identificationUnfinished_missingHost_impossible G remaining action
          component oneFreeComponent noContainingComponent)
  | shrink _fuel _remaining _outcome _action _current _actionNonempty
      _notAncestral _nested inductionHypothesis =>
      exact inductionHypothesis
  | restrict _fuel _remaining _outcome _action _current _component _larger
      _actionNonempty _ancestral _oneFreeComponent
      _severalRemainingComponents _componentNotMaximal _containingComponent
      _nested inductionHypothesis =>
      exact inductionHypothesis
  | product _fuel _remaining _outcome _action _current _component _component2
      _rest _piece _actionNonempty _ancestral _freeComponents
      _firstUnfinishedFactor _nested inductionHypothesis =>
      exact inductionHypothesis

end IdentificationUnfinishedTrace

theorem thinTowardForest_eq_cComponent_self
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep : Fin S.count) (fuel : Nat)
    (hY : nodes seedY = true) :
    thinTowardForest G nodes seedY seedKeep fuel =
      G.cComponentOf (thinTowardForest G nodes seedY seedKeep fuel) seedY := by
  rcases thinTowardForest_exists_host G nodes seedY seedKeep fuel hY with
    ⟨host, hHost, hEq⟩
  rw [hEq]
  exact (cComponentOf_idempotent G host hHost).symm

/--
When an outcome seed exists in the remaining set, the extracted large side
is the c-component of itself at that seed, so it is a legitimate forest host.
-/
theorem hedgeLargeOf_eq_cComponent_self
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seedY : Fin S.count}
    (hY : forestSeed q.outcome fail.remaining = some seedY) :
    hedgeLargeOf G q fail seedY = true ∧
      hedgeLargeOf G q fail =
        G.cComponentOf (hedgeLargeOf G q fail) seedY := by
  have hYmem : fail.remaining seedY = true :=
    forestSeed_mem q.outcome fail.remaining hY
  cases hX : NodeSet.firstMember (NodeSet.inter fail.remaining q.action) with
  | none =>
      constructor
      · simp [hedgeLargeOf, hY, hX]
        exact thinTowardForest_seed_mem G fail.remaining seedY seedY
          (NodeSet.members fail.remaining).length hYmem
      · simp [hedgeLargeOf, hY, hX]
        exact thinTowardForest_eq_cComponent_self G fail.remaining seedY seedY
          (NodeSet.members fail.remaining).length hYmem
  | some seedX =>
      constructor
      · simp [hedgeLargeOf, hY, hX]
        exact thinTowardForest_seed_mem G fail.remaining seedY seedX
          (NodeSet.members fail.remaining).length hYmem
      · simp [hedgeLargeOf, hY, hX]
        exact thinTowardForest_eq_cComponent_self G fail.remaining seedY seedX
          (NodeSet.members fail.remaining).length hYmem

namespace IdentificationUnfinishedTrace

/--
The fuel consumed by an unfinished trace never exceeds the rank of its root
invocation.  The proof groups all recursive shapes uniformly: shrink and 4.3
use strict host decrease, product uses its one-bit split bonus, and the
unmatched-host terminal is impossible.
-/
theorem fuel_le_identificationTraceRank
    {G : ObservedGraph S}
    {fuel : Nat} {remaining outcome action : NodeSet S}
    {current : ProbabilityTerm S}
    (trace :
      IdentificationUnfinishedTrace G fuel remaining outcome action current) :
    fuel ≤ identificationTraceRank G remaining action := by
  induction trace with
  | exhausted =>
      exact Nat.zero_le _
  | missingHost _fuel remaining _outcome action _current component
      _actionNonempty _ancestral oneFreeComponent
      _severalRemainingComponents _componentNotMaximal noContainingComponent =>
      exact False.elim
        (identificationUnfinished_missingHost_impossible G remaining action
          component oneFreeComponent noContainingComponent)
  | shrink fuel remaining outcome action _current _actionNonempty
      notAncestral _nested inductionHypothesis =>
      have rankDecreases :=
        identificationTraceRank_shrink_lt G remaining outcome action
          notAncestral
      omega
  | restrict fuel remaining _outcome action _current component larger
      _actionNonempty _ancestral _oneFreeComponent
      severalRemainingComponents _componentNotMaximal containingComponent
      _nested inductionHypothesis =>
      have rankDecreases :=
        identificationTraceRank_restrict_lt G remaining action component larger
          severalRemainingComponents containingComponent
      omega
  | product fuel remaining _outcome action _current component component2 rest
      piece _actionNonempty _ancestral freeComponents firstUnfinishedFactor
      _nested inductionHypothesis =>
      have rankDecreases :=
        identificationTraceRank_product_lt G remaining action component
          component2 rest piece freeComponents firstUnfinishedFactor.mem
      omega

end IdentificationUnfinishedTrace

/--
Any fuel strictly above the invocation rank rules out the executable
`unfinished` sentinel.  This is the reusable totality theorem for recursive
subcalls; it is independent of the larger public fuel formula.
-/
theorem identifyFuel_ne_unfinished_of_rank_lt
    {S : ObservedSignature.{0}} (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    (enoughFuel : identificationTraceRank G remaining action < fuel) :
    Legacy.identifyFuel fuel G remaining outcome action current ≠
      (IdentificationOutcome.unfinished : IdentificationOutcome S) := by
  intro unfinished
  let trace :=
    IdentificationUnfinishedTrace.of_eq_unfinished (S := S) fuel G remaining
      outcome action current unfinished
  have consumed := trace.fuel_le_identificationTraceRank
  omega

/-- The public cubic fuel allowance strictly exceeds the rank on `V`. -/
theorem identificationTraceRank_full_lt_identificationFuel
    (G : ObservedGraph S) (action : NodeSet S) :
    identificationTraceRank G NodeSet.full action < identificationFuel S := by
  cases countEq : S.count with
  | zero =>
      have enumeratedNil : NodeSet.enumerated S = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [NodeSet.length_enumerated, countEq]
      simp [identificationTraceRank, identificationFuel,
        ObservedGraph.cComponents, ObservedGraph.cComponentsCollect,
        NodeSet.members_full, enumeratedNil, countEq]
  | succ n =>
      have fullLength :
          (NodeSet.members (NodeSet.full : NodeSet S)).length = S.count := by
        rw [NodeSet.members_full, NodeSet.length_enumerated]
      have rankUpper := identificationTraceRank_upper G NodeSet.full action
      have countPositive : 0 < S.count := by omega
      have twoLeSucc : 2 ≤ Nat.succ S.count := by omega
      have firstProduct : S.count * 2 ≤ S.count * Nat.succ S.count :=
        Nat.mul_le_mul_left S.count twoLeSucc
      have cubicLower :
          (S.count * 2) * 2 ≤
            (S.count * Nat.succ S.count) * Nat.succ S.count :=
        Nat.mul_le_mul firstProduct twoLeSucc
      rw [fullLength] at rankUpper
      rw [identificationFuel]
      have linearStrict : 2 * S.count + 1 < 4 * S.count + 1 := by
        omega
      have cubicBound :
          4 * S.count ≤
            S.count * Nat.succ S.count * Nat.succ S.count := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using cubicLower
      omega

/-- Public joint identification never exhausts its constructive fuel bound. -/
theorem identifyJoint_ne_unfinished
    {S : ObservedSignature.{0}}
    (G : ObservedGraph S) (q : JointKernelQuery S) :
    Legacy.identifyJoint G q ≠ IdentificationOutcome.unfinished := by
  exact identifyFuel_ne_unfinished_of_rank_lt
    (identificationFuel S) G NodeSet.full q.outcome q.action
    (observationalJointTerm S)
    (identificationTraceRank_full_lt_identificationFuel G q.action)

/--
The total structural result of public joint ID.  Unlike
`JointIdentificationTrace`, this type has no implementation-sentinel branch:
the rank proof has discharged it once and for all.
-/
inductive JointIdentificationTerminalTrace
    (G : ObservedGraph S) (q : JointKernelQuery S)
  | identified (term : ProbabilityTerm S)
      (trace : JointIdentificationSuccessTrace G q term)
  | failed (fail : IdentificationFail S)
      (trace : JointIdentificationFailureTrace G q fail)

/-- Evaluate public ID and retain an exact success or failure trace. -/
noncomputable def identifyJoint_terminalTrace
    {S : ObservedSignature.{0}}
    (G : ObservedGraph S) (q : JointKernelQuery S) :
    JointIdentificationTerminalTrace G q := by
  cases result : Legacy.identifyJoint G q with
  | identified term =>
      exact .identified term
        (IdentificationSuccessTrace.of_eq_identified (identificationFuel S) G
          NodeSet.full q.outcome q.action (observationalJointTerm S) term result)
  | failed fail =>
      exact .failed fail
        (IdentificationFailureTrace.of_eq_failed (identificationFuel S) G
          NodeSet.full q.outcome q.action (observationalJointTerm S) result)
  | unfinished =>
      exact False.elim (identifyJoint_ne_unfinished G q result)

/-- Bayes-based conditional identification also cannot exhaust its joint fuel. -/
theorem identifyConditional_ne_unfinished
    {S : ObservedSignature.{0}}
    (G : ObservedGraph S) (q : ConditionalKernelQuery S) :
    Legacy.identifyConditional G q ≠ IdentificationOutcome.unfinished := by
  intro result
  have numeratorTotal := identifyJoint_ne_unfinished G q.jointNumerator
  have denominatorTotal := identifyJoint_ne_unfinished G q.jointDenominator
  cases numeratorResult : Legacy.identifyJoint G q.jointNumerator with
  | identified numerator =>
      cases denominatorResult : Legacy.identifyJoint G q.jointDenominator with
      | identified denominator =>
          simp [Legacy.identifyConditional, numeratorResult, denominatorResult] at result
      | failed fail =>
          simp [Legacy.identifyConditional, numeratorResult, denominatorResult] at result
      | unfinished =>
          exact denominatorTotal denominatorResult
  | failed fail =>
      cases denominatorResult : Legacy.identifyJoint G q.jointDenominator <;>
        simp [Legacy.identifyConditional, numeratorResult, denominatorResult] at result
  | unfinished =>
      exact numeratorTotal numeratorResult

/-- A self-c-component is a Boolean singleton partition. -/
theorem isSingleCComponent_of_self
    (G : ObservedGraph S) (nodes : NodeSet S) {seed : Fin S.count}
    (hseed : nodes seed = true)
    (hEq : nodes = G.cComponentOf nodes seed) :
    G.isSingleCComponent nodes = true := by
  have hs : G.cComponents nodes = [nodes] :=
    cComponents_eq_singleton G nodes hseed hEq
  simp [ObservedGraph.isSingleCComponent, hs]
  exact (NodeSet.equal_eq_true_iff nodes nodes).mpr rfl

theorem thinnedHedgeSelection_large_single
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seedY : Fin S.count}
    (hY : forestSeed q.outcome fail.remaining = some seedY) :
    G.isSingleCComponent (thinnedHedgeSelection G q fail).large = true := by
  have parts := hedgeLargeOf_eq_cComponent_self G q fail hY
  exact isSingleCComponent_of_self G _ parts.1 parts.2

theorem thinnedHedgeSelection_large_nonempty
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seedY : Fin S.count}
    (hY : forestSeed q.outcome fail.remaining = some seedY) :
    NodeSet.isEmpty (thinnedHedgeSelection G q fail).large = false :=
  isSingleCComponent_nonempty G _
    (thinnedHedgeSelection_large_single G q fail hY)

/--
The vertex tests of the thinned candidate, once an outcome seed exists
and the large side still meets the original action.
-/
theorem thinnedHedgeSelection_largeVerticesReady
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seedY : Fin S.count}
    (hY : forestSeed q.outcome fail.remaining = some seedY)
    (hmeets :
      NodeSet.meetsBool (thinnedHedgeSelection G q fail).large q.action =
        true) :
    largeVerticesReady G q (thinnedHedgeSelection G q fail).large = true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_, hmeets⟩
  refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
  · have hempty := thinnedHedgeSelection_large_nonempty G q fail hY
    cases h : NodeSet.isEmpty (thinnedHedgeSelection G q fail).large
    · rfl
    · exact False.elim (Bool.false_ne_true (hempty.symm.trans h))
  · exact thinnedHedgeSelection_large_single G q fail hY

theorem thinnedHedgeSelection_child_wellFormed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) :
    childWellFormedBool (thinnedHedgeSelection G q fail).large
      (thinnedHedgeSelection G q fail).child = true :=
  inducedChild_wellFormed _

/--
In a Boolean singleton c-component, every pair of selected vertices is
bidirected-reachable inside the set.
-/
theorem bidirectedReachableWithin_of_single
    (G : ObservedGraph S) (nodes : NodeSet S)
    (hsingle : G.isSingleCComponent nodes = true)
    {i j : Fin S.count}
    (hi : nodes i = true) (hj : nodes j = true) :
    G.bidirectedReachableWithin nodes i j = true := by
  rcases isSingleCComponent_spec G nodes hsingle with ⟨root, hroot, hEq⟩
  have hiComp : G.cComponentOf nodes root i = true := by
    rw [← hEq]
    exact hi
  have hjComp : G.cComponentOf nodes root j = true := by
    rw [← hEq]
    exact hj
  have hiConn : BidirectedConnectedWithin G nodes root i :=
    (cComponentOf_eq_true_iff G nodes hroot).mp hiComp
  have hjConn : BidirectedConnectedWithin G nodes root j :=
    (cComponentOf_eq_true_iff G nodes hroot).mp hjComp
  have ij : BidirectedConnectedWithin G nodes i j :=
    BidirectedConnectedWithin.trans (BidirectedConnectedWithin.symm hiConn)
      hjConn
  exact (bidirectedReachableWithin_eq_true_iff G nodes hi hj).mpr ij

/--
Thinning never drops a keep-seed that remains bidirected-reachable from
the outcome seed.  Each dropped extra child is chosen to preserve that
contact, so the keep-seed still meets the thinned forest.
-/
theorem thinTowardForest_keep_mem
    (G : ObservedGraph S) (nodes : NodeSet S)
    (seedY seedKeep : Fin S.count) (fuel : Nat)
    (hY : nodes seedY = true)
    (hKeep : G.bidirectedReachableWithin nodes seedY seedKeep = true) :
    thinTowardForest G nodes seedY seedKeep fuel seedKeep = true := by
  induction fuel generalizing nodes with
  | zero =>
      simp [thinTowardForest]
      exact hKeep
  | succ fuel ih =>
      cases hcond :
          atMostOneDirectedChildBool nodes &&
            G.bidirectedReachableWithin nodes seedY seedKeep with
      | true =>
          simp [thinTowardForest, hcond]
          exact hKeep
      | false =>
          cases hdrop : extraChildToDrop G nodes seedY seedKeep with
          | none =>
              simp [thinTowardForest, hcond, hdrop]
              exact hKeep
          | some child =>
              have hne : child ≠ seedY :=
                extraChildToDrop_ne_seedY G nodes seedY seedKeep child hdrop
              have inDiff :
                  NodeSet.diff nodes (NodeSet.singleton child) seedY = true := by
                refine Bool.and_eq_true_iff.mpr ⟨hY, ?_⟩
                have notChild : NodeSet.singleton child seedY = false :=
                  Bool.eq_false_iff.mpr fun htrue =>
                    hne ((NodeSet.singleton_eq_true_iff child seedY).mp
                      htrue).symm
                simp [notChild]
              have hKeepResidual :
                  G.cComponentOf
                    (NodeSet.diff nodes (NodeSet.singleton child)) seedY
                    seedKeep = true :=
                extraChildToDrop_keeps_contact G nodes seedY seedKeep child
                  hdrop
              have hY' :
                  G.cComponentOf
                    (NodeSet.diff nodes (NodeSet.singleton child))
                    seedY seedY = true :=
                cComponentOf_root_mem G _ inDiff
              have conn :
                  BidirectedConnectedWithin G
                    (NodeSet.diff nodes (NodeSet.singleton child))
                    seedY seedKeep :=
                (cComponentOf_eq_true_iff G
                  (NodeSet.diff nodes (NodeSet.singleton child)) inDiff).mp
                  hKeepResidual
              have connIn :
                  BidirectedConnectedWithin G
                    (G.cComponentOf
                      (NodeSet.diff nodes (NodeSet.singleton child)) seedY)
                    seedY seedKeep :=
                bidirectedConnected_within_cComponent G
                  (NodeSet.diff nodes (NodeSet.singleton child)) inDiff
                  conn hY'
              have hKeep' :
                  G.bidirectedReachableWithin
                    (G.cComponentOf
                      (NodeSet.diff nodes (NodeSet.singleton child)) seedY)
                    seedY seedKeep = true :=
                (bidirectedReachableWithin_eq_true_iff G
                  (G.cComponentOf
                    (NodeSet.diff nodes (NodeSet.singleton child)) seedY)
                  hY' hKeepResidual).mpr connIn
              have ihKeep :=
                ih
                  (G.cComponentOf
                    (NodeSet.diff nodes (NodeSet.singleton child)) seedY)
                  hY' hKeep'
              simpa [thinTowardForest, hcond, hdrop] using ihKeep

/--
When the remaining set is a single c-component and meets both an outcome
seed and an action seed, thinning keeps the action seed, so the large
side meets the original intervention.
-/
theorem hedgeLargeOf_meets_of_action_seed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seedY seedX : Fin S.count}
    (hY : forestSeed q.outcome fail.remaining = some seedY)
    (hX : NodeSet.firstMember (NodeSet.inter fail.remaining q.action) =
      some seedX)
    (hsingle : G.isSingleCComponent fail.remaining = true) :
    NodeSet.meetsBool (hedgeLargeOf G q fail) q.action = true := by
  have hYmem : fail.remaining seedY = true :=
    forestSeed_mem q.outcome fail.remaining hY
  have hInter : NodeSet.inter fail.remaining q.action seedX = true :=
    NodeSet.firstMember_mem hX
  have hXmem : fail.remaining seedX = true :=
    NodeSet.inter_subset_left _ q.action seedX hInter
  have hXact : q.action seedX = true :=
    NodeSet.inter_subset_right fail.remaining q.action seedX hInter
  have hconn :
      G.bidirectedReachableWithin fail.remaining seedY seedX = true :=
    bidirectedReachableWithin_of_single G fail.remaining hsingle hYmem hXmem
  have hKeep :
      hedgeLargeOf G q fail seedX = true := by
    simp [hedgeLargeOf, hY, hX]
    exact thinTowardForest_keep_mem G fail.remaining seedY seedX
      (NodeSet.members fail.remaining).length hYmem hconn
  exact (NodeSet.meetsBool_eq_true_iff _ _).mpr ⟨seedX, hKeep, hXact⟩

theorem thinnedHedgeSelection_largeVerticesReady_of_action_seed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seedY seedX : Fin S.count}
    (hY : forestSeed q.outcome fail.remaining = some seedY)
    (hX : NodeSet.firstMember (NodeSet.inter fail.remaining q.action) =
      some seedX)
    (hsingle : G.isSingleCComponent fail.remaining = true) :
    largeVerticesReady G q (thinnedHedgeSelection G q fail).large = true :=
  thinnedHedgeSelection_largeVerticesReady G q fail hY
    (hedgeLargeOf_meets_of_action_seed G q fail hY hX hsingle)

theorem thinnedHedgeSelection_largeVerticesReady_of_joint_fail
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (hfail : Legacy.identifyJoint G q = IdentificationOutcome.failed fail)
    {seedY seedX : Fin S.count}
    (hY : forestSeed q.outcome fail.remaining = some seedY)
    (hX : NodeSet.firstMember (NodeSet.inter fail.remaining q.action) =
      some seedX) :
    largeVerticesReady G q (thinnedHedgeSelection G q fail).large = true :=
  thinnedHedgeSelection_largeVerticesReady_of_action_seed G q fail hY hX
    (identifyJoint_eq_failed G q hfail)

/--
When the small side is the c-component of an outcome seed in `large \ X`,
it is a Boolean singleton partition of itself.
-/
theorem hedgeSmallOf_eq_cComponent_self
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seed : Fin S.count}
    (hseed :
      forestSeed q.outcome
        (NodeSet.diff (hedgeLargeOf G q fail) q.action) = some seed) :
    hedgeSmallOf G q fail seed = true ∧
      hedgeSmallOf G q fail =
        G.cComponentOf (hedgeSmallOf G q fail) seed := by
  have hmem :
      NodeSet.diff (hedgeLargeOf G q fail) q.action seed = true :=
    forestSeed_mem q.outcome _ hseed
  constructor
  · simp [hedgeSmallOf, hseed]
    exact cComponentOf_root_mem G _ hmem
  · simp [hedgeSmallOf, hseed]
    exact (cComponentOf_idempotent G _ hmem).symm

theorem thinnedHedgeSelection_small_single_of_seed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seed : Fin S.count}
    (hseed :
      forestSeed q.outcome
        (NodeSet.diff (hedgeLargeOf G q fail) q.action) = some seed) :
    G.isSingleCComponent (thinnedHedgeSelection G q fail).small = true := by
  have parts := hedgeSmallOf_eq_cComponent_self G q fail hseed
  exact isSingleCComponent_of_self G _ parts.1 parts.2

theorem thinnedHedgeSelection_small_nonempty_of_seed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seed : Fin S.count}
    (hseed :
      forestSeed q.outcome
        (NodeSet.diff (hedgeLargeOf G q fail) q.action) = some seed) :
    NodeSet.isEmpty (thinnedHedgeSelection G q fail).small = false :=
  isSingleCComponent_nonempty G _
    (thinnedHedgeSelection_small_single_of_seed G q fail hseed)

/--
An outcome seed that survives in the large forest is not in the action
(queries keep `X` and `Y` disjoint), so `large \ X` is nonempty and the
small-side forest seed exists.
-/
theorem hedgeSmallOf_seed_of_outcome_in_large
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seedY : Fin S.count}
    (hYout : q.outcome seedY = true)
    (hLarge : hedgeLargeOf G q fail seedY = true) :
    Exists fun seed =>
      forestSeed q.outcome
        (NodeSet.diff (hedgeLargeOf G q fail) q.action) = some seed := by
  have hnotX : q.action seedY = false := by
    cases ha : q.action seedY with
    | false => rfl
    | true =>
        have hout : q.outcome seedY = false :=
          q.action_outcome_disjoint seedY ha
        exact False.elim (Bool.false_ne_true (hout.symm.trans hYout))
  have inDiff :
      NodeSet.diff (hedgeLargeOf G q fail) q.action seedY = true :=
    Bool.and_eq_true_iff.mpr ⟨hLarge, by simp [hnotX]⟩
  have hempty :
      NodeSet.isEmpty
        (NodeSet.diff (hedgeLargeOf G q fail) q.action) = false :=
    (NodeSet.isEmpty_eq_false_iff _).mpr ⟨seedY, inDiff⟩
  exact forestSeed_of_nonempty q.outcome _ hempty

theorem thinnedHedgeSelection_small_single_of_outcome_seed
    (G : ObservedGraph S) (q : JointKernelQuery S)
    (fail : IdentificationFail S) {seedY : Fin S.count}
    (hY : forestSeed q.outcome fail.remaining = some seedY)
    (hYout : q.outcome seedY = true) :
    G.isSingleCComponent (thinnedHedgeSelection G q fail).small = true := by
  have hLarge : hedgeLargeOf G q fail seedY = true :=
    (hedgeLargeOf_eq_cComponent_self G q fail hY).1
  rcases hedgeSmallOf_seed_of_outcome_in_large G q fail hYout hLarge with
    ⟨seed, hseed⟩
  exact thinnedHedgeSelection_small_single_of_seed G q fail hseed

/--
The free side of an ID failure is a self-c-component of the remaining
host, so the failure-record selection has a Boolean singleton small side.
-/
theorem identifyFuel_eq_failed_free_self
    (fuel : Nat) (G : ObservedGraph S)
    (remaining outcome action : NodeSet S)
    (current : ProbabilityTerm S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyFuel fuel G remaining outcome action current =
      IdentificationOutcome.failed fail) :
    Exists fun root =>
      fail.free root = true ∧
        fail.free = G.cComponentOf fail.free root := by
  rcases (identifyFuel_eq_failed_free fuel G remaining outcome action
      current h).2 with ⟨host, root, hroot, hdef, _⟩
  have hmem : fail.free root = true := by
    rw [hdef]
    exact cComponentOf_root_mem G host hroot
  exact ⟨root, hmem, by
    rw [hdef]
    exact (cComponentOf_idempotent G host hroot).symm⟩

theorem identifyJoint_eq_failed_free
    (G : ObservedGraph S) (q : JointKernelQuery S)
    {fail : IdentificationFail S}
    (h : Legacy.identifyJoint G q = IdentificationOutcome.failed fail) :
    NodeSet.Subset fail.free fail.remaining ∧
      Exists fun root =>
        fail.free root = true ∧
          fail.free = G.cComponentOf fail.free root := by
  have parts :=
    identifyFuel_eq_failed_free (identificationFuel S) G NodeSet.full
      q.outcome q.action (observationalJointTerm S) h
  constructor
  · exact parts.1
  · exact identifyFuel_eq_failed_free_self (identificationFuel S) G
      NodeSet.full q.outcome q.action (observationalJointTerm S) h


end Causality
end Thesis
