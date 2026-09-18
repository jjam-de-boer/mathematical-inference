import Thesis.Causality.HardIntervention

namespace Thesis
namespace Causality

open Probability

/-!
Intrinsic finite-SCM query and identifiability semantics.

This module contains the graph-indexed model class, query languages, semantic
equivalence notions, finite counterexamples and hedge syntax.  Executable
c-component search and the Shpitser–Pearl ID recursion live in
`IdentificationSearch`.  External published theorem interfaces and certificate
transport live separately in `Thesis.CausalTransport.Correspondence`.
-/

def AssignmentsAgreeOn (nodes : NodeSet S)
    (x y : S.Assignment) : Prop :=
  forall i, nodes i = true -> x i = y i

def EventDependsOnlyOn (nodes : NodeSet S)
    (event : S.Assignment -> Bool) : Prop :=
  forall x y, AssignmentsAgreeOn nodes x y -> event x = event y

/-- Ordinary finite joint interventional query. -/
structure InterventionalQuery (S : ObservedSignature) where
  intervention : HardIntervention S
  outcomeNodes : NodeSet S
  action_outcome_disjoint :
    NodeSet.Disjoint intervention.targets outcomeNodes
  event : S.Assignment -> Bool
  event_local : EventDependsOnlyOn outcomeNodes event

/-- Conditional interventional query with an explicit conditioning event. -/
structure ConditionalQuery (S : ObservedSignature) where
  intervention : HardIntervention S
  outcomeNodes : NodeSet S
  conditionNodes : NodeSet S
  action_outcome_disjoint :
    NodeSet.Disjoint intervention.targets outcomeNodes
  action_condition_disjoint :
    NodeSet.Disjoint intervention.targets conditionNodes
  outcome_condition_disjoint :
    NodeSet.Disjoint outcomeNodes conditionNodes
  outcome : S.Assignment -> Bool
  condition : S.Assignment -> Bool
  outcome_local : EventDependsOnlyOn outcomeNodes outcome
  condition_local : EventDependsOnlyOn conditionNodes condition

/-- Distributional query `P(outcome | do(action))` used by completeness. -/
structure JointKernelQuery (S : ObservedSignature) where
  outcome : NodeSet S
  action : NodeSet S
  action_outcome_disjoint : NodeSet.Disjoint action outcome

/-- Distributional conditional query `P(outcome | do(action), condition)`. -/
structure ConditionalKernelQuery (S : ObservedSignature) where
  outcome : NodeSet S
  action : NodeSet S
  condition : NodeSet S
  action_outcome_disjoint : NodeSet.Disjoint action outcome
  action_condition_disjoint : NodeSet.Disjoint action condition
  outcome_condition_disjoint : NodeSet.Disjoint outcome condition

def InterventionalQuery.kernelQuery (q : InterventionalQuery S) :
    JointKernelQuery S where
  outcome := q.outcomeNodes
  action := q.intervention.targets
  action_outcome_disjoint := q.action_outcome_disjoint

def ConditionalQuery.kernelQuery (q : ConditionalQuery S) :
    ConditionalKernelQuery S where
  outcome := q.outcomeNodes
  action := q.intervention.targets
  condition := q.conditionNodes
  action_outcome_disjoint := q.action_outcome_disjoint
  action_condition_disjoint := q.action_condition_disjoint
  outcome_condition_disjoint := q.outcome_condition_disjoint

def JointKernelQuery.sourceTerm (q : JointKernelQuery S) : ProbabilityTerm S :=
  .kernel
    { outcome := q.outcome
      action := q.action
      condition := NodeSet.empty }

def ConditionalKernelQuery.sourceTerm (q : ConditionalKernelQuery S) :
    ProbabilityTerm S :=
  .kernel
    { outcome := q.outcome
      action := q.action
      condition := q.condition }

/-- The joint query `P(Y | do(X))` obtained by dropping the conditioner. -/
def ConditionalKernelQuery.unconditionalJoint
    (q : ConditionalKernelQuery S) : JointKernelQuery S where
  outcome := q.outcome
  action := q.action
  action_outcome_disjoint := q.action_outcome_disjoint

/-- An empty conditioner is the joint query `P(Y | do(X))`. -/
def ConditionalKernelQuery.toJoint (q : ConditionalKernelQuery S)
    (_emptyCondition : NodeSet.isEmpty q.condition = true) :
    JointKernelQuery S :=
  q.unconditionalJoint

theorem ConditionalKernelQuery.unconditionalJoint_sourceTerm
    (q : ConditionalKernelQuery S) :
    q.unconditionalJoint.sourceTerm =
      .kernel ⟨q.outcome, q.action, NodeSet.empty⟩ := by
  simp [ConditionalKernelQuery.unconditionalJoint,
    JointKernelQuery.sourceTerm]

theorem ConditionalKernelQuery.sourceTerm_eq_toJoint
    (q : ConditionalKernelQuery S)
    (emptyCondition : NodeSet.isEmpty q.condition = true) :
    q.sourceTerm = (q.toJoint emptyCondition).sourceTerm := by
  have hz : q.condition = NodeSet.empty :=
    NodeSet.eq_empty_of_isEmpty emptyCondition
  simp [ConditionalKernelQuery.sourceTerm,
    ConditionalKernelQuery.unconditionalJoint_sourceTerm,
    ConditionalKernelQuery.toJoint, hz]

/-- The query kernel is rule 1's left kernel at empty given-set. -/
theorem ConditionalKernelQuery.sourceTerm_eq_rule1Left_empty_w
    (q : ConditionalKernelQuery S) :
    q.sourceTerm =
      .kernel
        (rule1Left q.action q.outcome q.condition NodeSet.empty) := by
  simp [ConditionalKernelQuery.sourceTerm, rule1Left,
    NodeSet.union_empty_right]

/-- The query kernel is the conditioning rule's left kernel at empty
given-set: `P(Y | do(X), Z) = P(Y | do(X), Z ∪ ∅)`. -/
theorem ConditionalKernelQuery.sourceTerm_eq_conditioningLeft_empty_w
    (q : ConditionalKernelQuery S) :
    q.sourceTerm =
      .kernel ⟨q.outcome, q.action,
        NodeSet.union q.condition NodeSet.empty⟩ := by
  simp [ConditionalKernelQuery.sourceTerm, NodeSet.union_empty_right]

/-- Dropping the conditioner is rule 1's right kernel at empty given-set. -/
theorem ConditionalKernelQuery.unconditionalJoint_eq_rule1Right
    (q : ConditionalKernelQuery S) :
    q.unconditionalJoint.sourceTerm =
      .kernel
        (rule1Right q.action q.outcome q.condition NodeSet.empty) := by
  simp [ConditionalKernelQuery.unconditionalJoint,
    JointKernelQuery.sourceTerm, rule1Right]

/-- The joint query `P(Y | do(X ∪ Z))` obtained by intervening on the
conditioner. -/
def ConditionalKernelQuery.intervenedCondition
    (q : ConditionalKernelQuery S) : JointKernelQuery S where
  outcome := q.outcome
  action := NodeSet.union q.action q.condition
  action_outcome_disjoint := fun i hi =>
    match hx : q.action i with
    | true =>
        q.action_outcome_disjoint i hx
    | false =>
        have hz : q.condition i = true := by
          simp [NodeSet.union, hx] at hi
          exact hi
        match hy : q.outcome i with
        | false =>
            rfl
        | true =>
            False.elim
              (Bool.false_ne_true
                ((q.outcome_condition_disjoint i hy).symm.trans hz))

/-- The query kernel is rule 2's right kernel at empty given-set. -/
theorem ConditionalKernelQuery.sourceTerm_eq_rule2Right_empty_w
    (q : ConditionalKernelQuery S) :
    q.sourceTerm =
      .kernel
        (rule2Right q.action q.outcome q.condition NodeSet.empty) := by
  simp [ConditionalKernelQuery.sourceTerm, rule2Right,
    NodeSet.union_empty_right]

/-- Intervening on the conditioner is rule 2's left kernel at empty
given-set. -/
theorem ConditionalKernelQuery.intervenedCondition_eq_rule2Left
    (q : ConditionalKernelQuery S) :
    q.intervenedCondition.sourceTerm =
      .kernel
        (rule2Left q.action q.outcome q.condition NodeSet.empty) := by
  simp [ConditionalKernelQuery.intervenedCondition,
    JointKernelQuery.sourceTerm, rule2Left]

/-- The concrete kernel at the source of a joint distributional query. -/
def JointKernelQuery.operationKernel (query : JointKernelQuery S) : Kernel S where
  outcome := query.outcome
  action := query.action
  condition := NodeSet.empty

/-- The concrete kernel at the source of a conditional distributional query. -/
def ConditionalKernelQuery.operationKernel
    (query : ConditionalKernelQuery S) : Kernel S where
  outcome := query.outcome
  action := query.action
  condition := query.condition

@[simp] theorem JointKernelQuery.sourceTerm_eq_operationKernel
    (query : JointKernelQuery S) :
    query.sourceTerm = .kernel query.operationKernel :=
  rfl

@[simp] theorem ConditionalKernelQuery.sourceTerm_eq_operationKernel
    (query : ConditionalKernelQuery S) :
    query.sourceTerm = .kernel query.operationKernel :=
  rfl

noncomputable def JointKernelQuery.supportedAt (q : JointKernelQuery S)
    (model : ExactModel S) (assignment : S.Assignment) :
    q.sourceTerm.SupportedAt model assignment := by
  let value :=
    (Kernel.mk q.outcome q.action NodeSet.empty).distribution model assignment
  refine ⟨value.probVal (Kernel.agreesOn q.outcome assignment), ?_⟩
  simpa [JointKernelQuery.sourceTerm] using
    (Kernel.unconditionalDenote model q.outcome q.action assignment)

def JointKernelQuery.ValueEquivalent (q : JointKernelQuery S)
    (M N : ExactModel S) : Prop :=
  forall assignment,
    Nonempty (ProbabilityResult.Equivalent
      (q.sourceTerm.denote M assignment)
      (q.sourceTerm.denote N assignment))

/--
Full equivalence of the partial conditional-kernel results.  Unlike agreement
on common support, this also requires the two models to have the same support
status at every assignment.
-/
def ConditionalKernelQuery.ResultEquivalent (q : ConditionalKernelQuery S)
    (M N : ExactModel S) : Prop :=
  forall assignment,
    Nonempty (ProbabilityResult.Equivalent
      (q.sourceTerm.denote M assignment)
      (q.sourceTerm.denote N assignment))

/--
Agreement of conditional-kernel values at every assignment supported by both
models.  This relation does not assert that either model supports a given
assignment, nor that their support domains coincide.
-/
def ConditionalKernelQuery.AgreesOnCommonSupport
    (q : ConditionalKernelQuery S)
    (M N : ExactModel S) : Prop :=
  forall assignment,
    q.sourceTerm.SupportedAt M assignment ->
    q.sourceTerm.SupportedAt N assignment ->
    Nonempty (ProbabilityResult.Equivalent
      (q.sourceTerm.denote M assignment)
      (q.sourceTerm.denote N assignment))

/-- Conditional value equivalence means agreement on common support. -/
abbrev ConditionalKernelQuery.ValueEquivalent
    (q : ConditionalKernelQuery S) (M N : ExactModel S) : Prop :=
  q.AgreesOnCommonSupport M N

/-- Full partial-result equivalence entails agreement on common support. -/
theorem ConditionalKernelQuery.ResultEquivalent.agreesOnCommonSupport
    {q : ConditionalKernelQuery S} {M N : ExactModel S}
    (equivalent : q.ResultEquivalent M N) :
    q.AgreesOnCommonSupport M N := by
  intro assignment _ _
  exact equivalent assignment

def InterventionalQuery.distribution (q : InterventionalQuery S)
    (M : ExactModel S) : FiniteProbRecord S.Assignment :=
  if finAny S.count q.intervention.targets then
    M.interventionalDist q.intervention.value
  else M.observationalDist

def ConditionalQuery.distribution (q : ConditionalQuery S)
    (M : ExactModel S) : FiniteProbRecord S.Assignment :=
  if finAny S.count q.intervention.targets then
    M.interventionalDist q.intervention.value
  else M.observationalDist

def InterventionalQuery.value (q : InterventionalQuery S)
    (M : ExactModel S) : QProb :=
  (q.distribution M).probVal q.event

theorem InterventionalQuery.referenceFor_eq_on_outcome
    (q : InterventionalQuery S) (assignment : S.Assignment)
    (i : Fin S.count) (selected : q.outcomeNodes i = true) :
    q.intervention.referenceFor assignment i = assignment i := by
  apply q.intervention.referenceFor_eq_of_target_false assignment i
  cases target : q.intervention.targets i with
  | false => rfl
  | true =>
      have := q.action_outcome_disjoint i target
      rw [selected] at this
      contradiction

theorem InterventionalQuery.agreesOn_referenceFor
    (q : InterventionalQuery S) (assignment sample : S.Assignment) :
    Kernel.agreesOn q.outcomeNodes
        (q.intervention.referenceFor assignment) sample =
      Kernel.agreesOn q.outcomeNodes assignment sample := by
  apply finAll_congr
  intro i
  cases selected : q.outcomeNodes i with
  | false => simp
  | true =>
      rw [q.referenceFor_eq_on_outcome assignment i selected]

theorem InterventionalQuery.kernel_distribution_referenceFor
    (q : InterventionalQuery S) (model : ExactModel S)
    (assignment : S.Assignment) :
    (Kernel.mk q.outcomeNodes q.intervention.targets NodeSet.empty).distribution
        model (q.intervention.referenceFor assignment) =
      q.distribution model := by
  simp only [Kernel.distribution, Kernel.hasAction, distribution]
  rw [q.intervention.intervention_referenceFor q.outcomeNodes
    NodeSet.empty assignment]
  rfl

noncomputable def InterventionalQuery.cellDenote
    (q : InterventionalQuery S) (model : ExactModel S)
    (assignment : S.Assignment) :
    ProbabilityResult.Equivalent
      (q.kernelQuery.sourceTerm.denote model
        (q.intervention.referenceFor assignment))
      (some ((q.distribution model).probVal
        (Kernel.agreesOn q.outcomeNodes assignment))) := by
  let base := Kernel.unconditionalDenote model q.outcomeNodes
    q.intervention.targets (q.intervention.referenceFor assignment)
  have cellEquivalent : QProb.Equiv
      (((Kernel.mk q.outcomeNodes q.intervention.targets NodeSet.empty).distribution
        model (q.intervention.referenceFor assignment)).probVal
          (Kernel.agreesOn q.outcomeNodes
            (q.intervention.referenceFor assignment)))
      ((q.distribution model).probVal
        (Kernel.agreesOn q.outcomeNodes assignment)) := by
    rw [q.kernel_distribution_referenceFor model assignment]
    exact FiniteProbRecord.probVal_congr _ _ _ (fun sample =>
      q.agreesOn_referenceFor assignment sample)
  exact ProbabilityResult.trans base (.value cellEquivalent)

def InterventionalQuery.projectedDistribution
    (q : InterventionalQuery S) (model : ExactModel S) :
    FiniteProbRecord S.Assignment :=
  (q.distribution model).map (S.project q.outcomeNodes)

theorem InterventionalQuery.projectedSingleton_equiv_cell
    (q : InterventionalQuery S) (model : ExactModel S)
    (assignment : S.Assignment)
    (canonical : S.project q.outcomeNodes assignment = assignment) :
    QProb.Equiv
      ((q.projectedDistribution model).probVal
        (FiniteProbRecord.singletonEvent assignment))
      ((q.distribution model).probVal
        (Kernel.agreesOn q.outcomeNodes assignment)) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.map_probVal (q.distribution model)
      (S.project q.outcomeNodes)
      (FiniteProbRecord.singletonEvent assignment))
    (FiniteProbRecord.probVal_congr (q.distribution model) _ _
      (fun sample => by
        have cell := Kernel.singleton_project_event
          q.outcomeNodes assignment sample
        rw [canonical] at cell
        exact cell))

theorem InterventionalQuery.projectedSingleton_equiv_zero
    (q : InterventionalQuery S) (model : ExactModel S)
    (assignment : S.Assignment)
    (noncanonical : S.project q.outcomeNodes assignment ≠ assignment) :
    QProb.Equiv
      ((q.projectedDistribution model).probVal
        (FiniteProbRecord.singletonEvent assignment))
      QProb.zero := by
  exact QProb.equiv_trans
    (FiniteProbRecord.map_probVal (q.distribution model)
      (S.project q.outcomeNodes)
      (FiniteProbRecord.singletonEvent assignment))
    (QProb.equiv_trans
      (FiniteProbRecord.probVal_congr (q.distribution model) _ _
        (fun sample => by
          have impossible : S.project q.outcomeNodes sample ≠ assignment := by
            intro same
            apply noncanonical
            rw [← same]
            exact S.project_idempotent q.outcomeNodes sample
          exact decide_eq_false impossible))
      (FiniteProbRecord.probVal_false (q.distribution model)))

theorem InterventionalQuery.projectedSingleton_equiv
    (q : InterventionalQuery S) (left right : ExactModel S)
    (kernelEquivalent : q.kernelQuery.ValueEquivalent left right)
    (assignment : S.Assignment) :
    QProb.Equiv
      ((q.projectedDistribution left).probVal
        (FiniteProbRecord.singletonEvent assignment))
      ((q.projectedDistribution right).probVal
        (FiniteProbRecord.singletonEvent assignment)) := by
  by_cases canonical : S.project q.outcomeNodes assignment = assignment
  · let leftCell := q.cellDenote left assignment
    let rightCell := q.cellDenote right assignment
    rcases kernelEquivalent (q.intervention.referenceFor assignment) with
      ⟨sourceEquivalent⟩
    have cellEquivalent : QProb.Equiv
        ((q.distribution left).probVal
          (Kernel.agreesOn q.outcomeNodes assignment))
        ((q.distribution right).probVal
          (Kernel.agreesOn q.outcomeNodes assignment)) := by
      have result := ProbabilityResult.trans (ProbabilityResult.symm leftCell)
        (ProbabilityResult.trans sourceEquivalent rightCell)
      cases result with
      | value equivalent => exact equivalent
    exact QProb.equiv_trans
      (q.projectedSingleton_equiv_cell left assignment canonical)
      (QProb.equiv_trans cellEquivalent
        (QProb.equiv_symm
          (q.projectedSingleton_equiv_cell right assignment canonical)))
  · exact QProb.equiv_trans
      (q.projectedSingleton_equiv_zero left assignment canonical)
      (QProb.equiv_symm
        (q.projectedSingleton_equiv_zero right assignment canonical))

theorem InterventionalQuery.projectedEvent_equiv_value
    (q : InterventionalQuery S) (model : ExactModel S) :
    QProb.Equiv ((q.projectedDistribution model).probVal q.event)
      (q.value model) := by
  exact QProb.equiv_trans
    (FiniteProbRecord.map_probVal (q.distribution model)
      (S.project q.outcomeNodes) q.event)
    (FiniteProbRecord.probVal_congr (q.distribution model) _ _
      (fun sample =>
        q.event_local (S.project q.outcomeNodes sample) sample (fun i selected =>
          by simp [ObservedSignature.project, selected])))

def ConditionalQuery.denominator (q : ConditionalQuery S)
    (M : ExactModel S) : QProb :=
  (q.distribution M).probVal q.condition

def ConditionalQuery.numerator (q : ConditionalQuery S)
    (M : ExactModel S) : QProb :=
  (q.distribution M).probVal
    (fun x => q.outcome x && q.condition x)

def ConditionalQuery.value (q : ConditionalQuery S)
    (M : ExactModel S) (supported : 0 < (q.denominator M).num) : QProb :=
  QProb.div (q.numerator M) (q.denominator M) supported

/-- Equality of conditional ratios without quotient equality or proof casts. -/
def ConditionalQuery.ValueEquivalent (q : ConditionalQuery S)
    (M N : ExactModel S) : Prop :=
  QProb.Equiv
    (QProb.mul (q.numerator M) (q.denominator N))
    (QProb.mul (q.numerator N) (q.denominator M))

/-- Agreement of the projected graph with a fixed observed ADMG. -/
def HasProjectedGraph (M : ExactModel S) (G : ObservedGraph S) : Prop :=
  forall i j, M.observedGraph.bidirected i j = G.bidirected i j

/-- The exact finite canonical semi-Markovian model class used for transport. -/
def Compatible (M : ExactModel S) (G : ObservedGraph S) : Prop :=
  M.IsCanonicalSemiMarkovian /\ HasProjectedGraph M G

def ObservationallyEquivalent (M N : ExactModel S) : Prop :=
  ProbabilityTerm.ObservationalAgreement M N

/--
Strict positivity of the observed joint.

Every complete observed assignment carries positive mass.  Sequential
observational conditionals used by ID/IDC are then defined at every
reference assignment.  This is a regularity hypothesis of identification,
not a constraint on the SCM layer: `Compatible` continues to admit zeros.
-/
def ObservationallyPositive (M : ExactModel S) : Prop :=
  forall assignment : S.Assignment,
    0 <
      (M.observationalDist.probVal
        (FiniteProbRecord.singletonEvent assignment)).num

/--
Every observational cylinder inherits strict positivity from the atoms.

A sequential conditional `P(v_i | earlier)` has denominator equal to a
cylinder on the conditioner set.  Under `ObservationallyPositive` that
denominator is therefore never zero, so ID's chain-rule factors are defined
at every reference assignment.
-/
theorem ObservationallyPositive.cylinder_positive
    {M : ExactModel S} (positive : ObservationallyPositive M)
    (nodes : NodeSet S) (reference : S.Assignment) :
    0 <
      (M.observationalDist.probVal
        (Kernel.agreesOn nodes reference)).num := by
  have subset : forall sample,
      FiniteProbRecord.singletonEvent reference sample = true ->
        Kernel.agreesOn nodes reference sample = true := by
    intro sample hSingleton
    have same : sample = reference := by
      simpa [FiniteProbRecord.singletonEvent] using hSingleton
    simpa [same] using Kernel.agreesOn_refl nodes reference
  have mono :
      (M.observationalDist.probVal
        (FiniteProbRecord.singletonEvent reference)).num ≤
        (M.observationalDist.probVal
          (Kernel.agreesOn nodes reference)).num :=
    FiniteProbRecord.eventMass_mono M.observationalDist.atoms
      (FiniteProbRecord.singletonEvent reference)
      (Kernel.agreesOn nodes reference) subset
  exact Nat.lt_of_lt_of_le (positive reference) mono

/--
A selected class of exact models over one observed ADMG.

Identification, certificates, and completeness are stated relative to such
a class.  The SCM layer (`Compatible`) stays general; positivity and other
regularity hypotheses are added here and then specialised.
-/
structure GraphModelClass.{u} {S : ObservedSignature.{u}}
    (G : ObservedGraph S) where
  Mem : ExactModel.{u} S -> Prop
  mem_compatible :
    forall (model : ExactModel.{u} S), Mem model -> Compatible model G

namespace GraphModelClass

variable {S : ObservedSignature}

/-- Every canonical semi-Markovian model with the given projected graph. -/
def all (G : ObservedGraph S) : GraphModelClass G where
  Mem := fun model => Compatible model G
  mem_compatible := fun _model member => member

/--
The classical identification class: compatible models whose observed joint
is strictly positive.  Shpitser–Pearl / Huang–Valtorta completeness is
stated for this class, once the signature is also `ValueRich`.
-/
def positive (G : ObservedGraph S) : GraphModelClass G where
  Mem := fun model => Compatible model G /\ ObservationallyPositive model
  mem_compatible := fun _model member => member.1

/-- Class `C` is contained in class `D`. -/
def Subset {G : ObservedGraph S} (C D : GraphModelClass G) : Prop :=
  forall model, C.Mem model -> D.Mem model

theorem positive_subset_all (G : ObservedGraph S) :
    (positive G).Subset (all G) := by
  intro model member
  exact member.1

/-- Joint identifiability inside a selected model class. -/
def identifiable {G : ObservedGraph S} (C : GraphModelClass G)
    (q : JointKernelQuery S) : Prop :=
  forall (M N : ExactModel S),
    C.Mem M ->
    C.Mem N ->
    ObservationallyEquivalent M N ->
    q.ValueEquivalent M N

/--
Conditional identifiability inside a selected model class.

As in the unrestricted case, this is agreement on common support rather
than full partial-result equality.
-/
def conditionalIdentifiable {G : ObservedGraph S} (C : GraphModelClass G)
    (q : ConditionalKernelQuery S) : Prop :=
  forall (M N : ExactModel S),
    C.Mem M ->
    C.Mem N ->
    ObservationallyEquivalent M N ->
    q.ValueEquivalent M N

def eventIdentifiable {G : ObservedGraph S} (C : GraphModelClass G)
    (q : InterventionalQuery S) : Prop :=
  forall (M N : ExactModel S),
    C.Mem M ->
    C.Mem N ->
    ObservationallyEquivalent M N ->
    QProb.Equiv (q.value M) (q.value N)

def eventConditionalSupported {G : ObservedGraph S} (C : GraphModelClass G)
    (q : ConditionalQuery S) : Prop :=
  forall M : ExactModel S, C.Mem M -> 0 < (q.denominator M).num

def eventConditionalIdentifiable {G : ObservedGraph S} (C : GraphModelClass G)
    (q : ConditionalQuery S) : Prop :=
  forall (M N : ExactModel S),
    C.Mem M ->
    C.Mem N ->
    ObservationallyEquivalent M N ->
    0 < (q.denominator M).num ->
    0 < (q.denominator N).num ->
    q.ValueEquivalent M N

/-- Agreement on a larger class implies agreement on every subclass. -/
theorem identifiable_of_subset {G : ObservedGraph S}
    {C D : GraphModelClass G}
    (subset : C.Subset D) (q : JointKernelQuery S)
    (identifiable : D.identifiable q) : C.identifiable q := by
  intro left right leftMem rightMem observational
  exact identifiable left right (subset left leftMem) (subset right rightMem)
    observational

theorem conditionalIdentifiable_of_subset {G : ObservedGraph S}
    {C D : GraphModelClass G}
    (subset : C.Subset D) (q : ConditionalKernelQuery S)
    (identifiable : D.conditionalIdentifiable q) :
    C.conditionalIdentifiable q := by
  intro left right leftMem rightMem observational
  exact identifiable left right (subset left leftMem) (subset right rightMem)
    observational

/-- Identifiability in the unrestricted compatible class specialises to the
positive subclass. -/
theorem positive_identifiable_of_all (G : ObservedGraph S)
    (q : JointKernelQuery S)
    (identifiable : (all G).identifiable q) :
    (positive G).identifiable q :=
  identifiable_of_subset (positive_subset_all G) q identifiable

theorem positive_conditionalIdentifiable_of_all (G : ObservedGraph S)
    (q : ConditionalKernelQuery S)
    (identifiable : (all G).conditionalIdentifiable q) :
    (positive G).conditionalIdentifiable q :=
  conditionalIdentifiable_of_subset (positive_subset_all G) q identifiable

/-- Full kernel identifiability in a class entails every local fixed-event instance. -/
theorem kernel_identifiable_implies_event {G : ObservedGraph S}
    (C : GraphModelClass G) (q : InterventionalQuery S)
    (kernelIdentifiable : C.identifiable q.kernelQuery) :
    C.eventIdentifiable q := by
  intro left right leftMem rightMem observational
  have kernelEquivalent := kernelIdentifiable left right leftMem rightMem
    observational
  have projectedEquivalent : QProb.Equiv
      ((q.projectedDistribution left).probVal q.event)
      ((q.projectedDistribution right).probVal q.event) :=
    FiniteProbRecord.probVal_extensional_of_singletons
      (q.projectedDistribution left) (q.projectedDistribution right)
      S.assignmentEnumeration S.assignmentEnumeration_nodup
      S.assignmentEnumeration_complete
      (q.projectedSingleton_equiv left right kernelEquivalent) q.event
  exact QProb.equiv_trans
    (QProb.equiv_symm (q.projectedEvent_equiv_value left))
    (QProb.equiv_trans projectedEquivalent
      (q.projectedEvent_equiv_value right))

end GraphModelClass

/-- Event-level identifiability is the derived fixed-event application notion. -/
abbrev EventIdentifiable (G : ObservedGraph S) (q : InterventionalQuery S) :
    Prop :=
  (GraphModelClass.all G).eventIdentifiable q

abbrev EventConditionalSupported (G : ObservedGraph S)
    (q : ConditionalQuery S) : Prop :=
  (GraphModelClass.all G).eventConditionalSupported q

abbrev EventConditionalIdentifiable (G : ObservedGraph S)
    (q : ConditionalQuery S) : Prop :=
  (GraphModelClass.all G).eventConditionalIdentifiable q

/--
Distributional identifiability over every compatible model, including those
with observational zeros.  Classical completeness is *not* claimed for this
class; use `GraphModelClass.positive` for the Shpitser–Pearl specialisation.
-/
abbrev Identifiable (G : ObservedGraph S) (q : JointKernelQuery S) : Prop :=
  (GraphModelClass.all G).identifiable q

/--
A conditional kernel is identifiable when every pair of compatible,
observationally equivalent models agrees at each assignment supported by both
models.  This common-support notion does not require global support or equality
of support domains; `ConditionalKernelQuery.ResultEquivalent` expresses the
stronger full partial-result comparison.
-/
abbrev ConditionalIdentifiable (G : ObservedGraph S)
    (q : ConditionalKernelQuery S) : Prop :=
  (GraphModelClass.all G).conditionalIdentifiable q

/-- Full kernel identifiability entails every local fixed-event instance. -/
theorem kernel_identifiable_implies_event_identifiable
    (G : ObservedGraph S) (q : InterventionalQuery S)
    (kernelIdentifiable : Identifiable G q.kernelQuery) :
    EventIdentifiable G q :=
  (GraphModelClass.all G).kernel_identifiable_implies_event q kernelIdentifiable

/--
An explicit finite rational witness that a query is not identifiable inside
a selected model class.  Both models are required to belong to the class, so
a positivity-restricted completeness package cannot discharge a hedge by
leaving the regular subclass.
-/
structure CounterexampleIn {S : ObservedSignature} {G : ObservedGraph S}
    (C : GraphModelClass G) (q : JointKernelQuery S) where
  left : ExactModel S
  right : ExactModel S
  left_mem : C.Mem left
  right_mem : C.Mem right
  observationally_equal : ObservationallyEquivalent left right
  query_separated : Not (q.ValueEquivalent left right)

theorem CounterexampleIn.not_identifiable
    {S : ObservedSignature} {G : ObservedGraph S} {C : GraphModelClass G}
    {q : JointKernelQuery S}
    (counterexample : CounterexampleIn C q) :
    Not (C.identifiable q) := by
  intro identifiable
  exact counterexample.query_separated
    (identifiable counterexample.left counterexample.right
      counterexample.left_mem counterexample.right_mem
      counterexample.observationally_equal)

/-- Unrestricted compatible counterexample, recovered as the `all` class. -/
abbrev Counterexample (G : ObservedGraph S) (q : JointKernelQuery S) :=
  CounterexampleIn (GraphModelClass.all G) q

theorem Counterexample.not_identifiable
    (counterexample : Counterexample G q) :
    Not (Identifiable G q) :=
  CounterexampleIn.not_identifiable counterexample

/-! ## Finite c-components, c-forests, and hedges -/

inductive DirectedReachableBy (S : ObservedSignature)
    (edge : Fin S.count -> Fin S.count -> Prop) :
    Fin S.count -> Fin S.count -> Prop
  | refl (i) : DirectedReachableBy S edge i i
  | tail {i j k} :
      DirectedReachableBy S edge i j -> edge j k ->
        DirectedReachableBy S edge i k

namespace DirectedReachableBy

theorem trans {S : ObservedSignature}
    {edge : Fin S.count -> Fin S.count -> Prop}
    {i j k : Fin S.count}
    (first : DirectedReachableBy S edge i j)
    (second : DirectedReachableBy S edge j k) :
    DirectedReachableBy S edge i k := by
  induction second with
  | refl => exact first
  | tail _prev ek ih => exact .tail ih ek

/-- Prepend a single edge onto an existing directed walk. -/
theorem step_left {S : ObservedSignature}
    {edge : Fin S.count -> Fin S.count -> Prop}
    {i j k : Fin S.count}
    (first : edge i j) (rest : DirectedReachableBy S edge j k) :
    DirectedReachableBy S edge i k :=
  trans (.tail (.refl i) first) rest

end DirectedReachableBy

inductive BidirectedConnectedWithin (G : ObservedGraph S) (nodes : NodeSet S) :
    Fin S.count -> Fin S.count -> Prop
  | refl {i} : nodes i = true -> BidirectedConnectedWithin G nodes i i
  | tail {i j k} :
      BidirectedConnectedWithin G nodes i j ->
      nodes k = true -> G.bidirected j k = true ->
      BidirectedConnectedWithin G nodes i k

namespace BidirectedConnectedWithin

theorem mem_left {G : ObservedGraph S} {nodes : NodeSet S} {i j : Fin S.count}
    (h : BidirectedConnectedWithin G nodes i j) : nodes i = true := by
  induction h with
  | refl selected => exact selected
  | tail _prev _selected _edge ih => exact ih

theorem mem_right {G : ObservedGraph S} {nodes : NodeSet S} {i j : Fin S.count}
    (h : BidirectedConnectedWithin G nodes i j) : nodes j = true := by
  induction h with
  | refl selected => exact selected
  | tail _prev selected _edge _ih => exact selected

theorem trans {G : ObservedGraph S} {nodes : NodeSet S}
    {i j k : Fin S.count}
    (first : BidirectedConnectedWithin G nodes i j)
    (second : BidirectedConnectedWithin G nodes j k) :
    BidirectedConnectedWithin G nodes i k := by
  induction second with
  | refl _selected => exact first
  | tail _prev selected edge ih => exact .tail ih selected edge

/-- Bidirected walks reverse because the ADMG bidirected relation is symmetric. -/
theorem symm {G : ObservedGraph S} {nodes : NodeSet S} {i j : Fin S.count}
    (h : BidirectedConnectedWithin G nodes i j) :
    BidirectedConnectedWithin G nodes j i := by
  induction h with
  | refl selected => exact .refl selected
  | tail prev selected edge ih =>
      exact trans
        (.tail (.refl selected) (mem_right prev)
          (G.bidirected_symmetric edge))
        ih

end BidirectedConnectedWithin

def BidirectedComponent (G : ObservedGraph S) (nodes : NodeSet S) : Prop :=
  (Exists fun i => nodes i = true) /\
    forall i j,
      nodes i = true -> nodes j = true ->
      BidirectedConnectedWithin G nodes i j

def AtMostOneDirectedChild (_G : ObservedGraph S) (nodes : NodeSet S) : Prop :=
  forall parent child₁ child₂,
    nodes parent = true ->
    nodes child₁ = true ->
    nodes child₂ = true ->
    S.directed parent child₁ = true ->
    S.directed parent child₂ = true ->
    child₁ = child₂

def IsRootIn (_G : ObservedGraph S) (nodes : NodeSet S)
    (root : Fin S.count) : Prop :=
  nodes root = true /\
    forall child,
      nodes child = true -> S.directed root child = false

/--
Kept directed successor of a c-forest.  `none` is a forest root, or a vertex
outside the selected set.  At most one child is structural in `Option`.
-/
abbrev ForestChild (S : ObservedSignature) :=
  Fin S.count -> Option (Fin S.count)

/-- Restrict a child map to a vertex subset: unselected parents keep `none`. -/
def restrictChild (nodes : NodeSet S) (child : ForestChild S) :
    ForestChild S :=
  fun i => if nodes i then child i else none

theorem restrictChild_of_false {nodes : NodeSet S} {child : ForestChild S}
    {i : Fin S.count} (h : nodes i = false) :
    restrictChild nodes child i = none := by
  unfold restrictChild
  simp [h]

theorem restrictChild_of_true {nodes : NodeSet S} {child : ForestChild S}
    {i : Fin S.count} (h : nodes i = true) :
    restrictChild nodes child i = child i := by
  unfold restrictChild
  simp [h]

/--
A C-forest is a subgraph, not an induced node selection: bidirected edges
stay those of `G` on `nodes`, while directed edges are the kept child map.
-/
structure CForest (G : ObservedGraph S)
    (nodes roots : NodeSet S) (child : ForestChild S) : Prop where
  component : BidirectedComponent G nodes
  child_off_set :
    forall parent, nodes parent = false -> child parent = none
  child_edge :
    forall parent c,
      child parent = some c ->
        nodes parent = true ∧
          nodes c = true ∧
            S.directed parent c = true
  roots_exact :
    forall i, roots i = true ↔ (nodes i = true ∧ child i = none)

/-- A subset of a one-child selection still has at most one selected child. -/
theorem AtMostOneDirectedChild.of_subset {G : ObservedGraph S}
    {large small : NodeSet S}
    (h : AtMostOneDirectedChild G large)
    (sub : NodeSet.Subset small large) :
    AtMostOneDirectedChild G small := by
  intro parent child₁ child₂ hp h1 h2 e1 e2
  exact h parent child₁ child₂ (sub parent hp) (sub child₁ h1) (sub child₂ h2) e1 e2

/--
The finite hedge obstruction for an ordinary interventional query.

`child` is stored once, on the large forest.  The small forest is the
restriction of that map to a child-closed subset of `large \ X`, so `F'` is
a subgraph of `F` in the 2006 sense.

`actionSeed` and `outcomeSeed` are Type-level vertices recovered from
Boolean member lists (intersection of the large side with `X`, and a
reached outcome of a kept sink).  They are not unpackings of the `Prop`
fields `large_meets_intervention` and `roots_reach_outcome`, which remain
for theorem-level reasoning.
-/
structure HedgeWitness (G : ObservedGraph S)
    (q : JointKernelQuery S) where
  large : NodeSet S
  small : NodeSet S
  roots : NodeSet S
  child : ForestChild S
  large_forest : CForest G large roots child
  small_forest : CForest G small roots (restrictChild small child)
  small_subset_large : NodeSet.Subset small large
  large_meets_intervention : NodeSet.Meets large q.action
  small_avoids_intervention : NodeSet.Disjoint small q.action
  roots_reach_outcome :
    forall root,
      roots root = true ->
      Exists fun outcome =>
        q.outcome outcome = true /\
          DirectedReachableBy S
            (fun i j =>
              mutilatedDirected S q.action i j = true)
            root outcome
  /--
  An action vertex on the large forest, recovered from the member list of
  `large ∩ X`.  Stored as data so a countermodel constructor can mention
  it without eliminating `Meets`/`Exists` into `Type`.
  -/
  actionSeed : Fin S.count
  actionSeed_in_large : large actionSeed = true
  actionSeed_in_action : q.action actionSeed = true
  /--
  An outcome vertex reached, along mutilated directed edges, from a kept
  sink of the large forest.  Recovered from `rootsReachOutcomeBool` by
  list search, not from unpacking `roots_reach_outcome`.
  -/
  outcomeSeed : Fin S.count
  outcomeSeed_in_outcome : q.outcome outcomeSeed = true

/-! ## Intrinsic type-theoretic target -/

/-- Semantic agreement avoids extensional equality of functions and records. -/
structure ModelAgreement (left right : ExactModel S) : Prop where
  observational : forall event,
    QProb.Equiv
      (left.observationalValue event) (right.observationalValue event)
  interventional : forall target event,
    QProb.Equiv
      (left.interventionalValue target event)
      (right.interventionalValue target event)
  projectedGraph : forall i j,
    left.observedGraph.bidirected i j = right.observedGraph.bidirected i j

/-- The target model is the dependent finite SCM record itself. -/
abbrev TypeTheoreticModel (S : ObservedSignature) := ExactModel S

abbrev TypeTheoreticCompatible (G : ObservedGraph S)
    (M : TypeTheoreticModel S) : Prop := Compatible M G

abbrev TypeTheoreticObsEq (M N : TypeTheoreticModel S) : Prop :=
  ObservationallyEquivalent M N

abbrev TypeTheoreticIdentifiable (G : ObservedGraph S)
    (q : JointKernelQuery S) : Prop := Identifiable G q

abbrev TypeTheoreticConditionalIdentifiable (G : ObservedGraph S)
    (q : ConditionalKernelQuery S) : Prop := ConditionalIdentifiable G q

abbrev TypeTheoreticEventIdentifiable (G : ObservedGraph S)
    (q : InterventionalQuery S) : Prop := EventIdentifiable G q

/-- Type-theoretic identifiability inside a selected model class. -/
abbrev TypeTheoreticIdentifiableIn {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (q : JointKernelQuery S) : Prop := C.identifiable q

abbrev TypeTheoreticConditionalIdentifiableIn {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (q : ConditionalKernelQuery S) : Prop := C.conditionalIdentifiable q

abbrev TypeTheoreticEventIdentifiableIn {S : ObservedSignature}
    {G : ObservedGraph S} (C : GraphModelClass G)
    (q : InterventionalQuery S) : Prop := C.eventIdentifiable q

theorem typeTheoretic_kernel_identifiable_implies_event
    (G : ObservedGraph S) (q : InterventionalQuery S)
    (kernelIdentifiable : TypeTheoreticIdentifiable G q.kernelQuery) :
    TypeTheoreticEventIdentifiable G q :=
  kernel_identifiable_implies_event_identifiable G q kernelIdentifiable

end Causality
end Thesis
