import Thesis.Causality.HardIntervention

namespace Thesis
namespace Causality

open Probability

/-!
Intrinsic finite-SCM query and identifiability semantics.

This module contains the graph-indexed model class, query languages, semantic
equivalence notions, finite counterexamples and hedge syntax.  External
published theorem interfaces and certificate transport live separately in
`Thesis.CausalTransport.Correspondence`.
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

/-- Event-level identifiability is the derived fixed-event application notion. -/
def EventIdentifiable (G : ObservedGraph S) (q : InterventionalQuery S) : Prop :=
  forall (M N : ExactModel S),
    Compatible M G ->
    Compatible N G ->
    ObservationallyEquivalent M N ->
    QProb.Equiv (q.value M) (q.value N)

def EventConditionalSupported (G : ObservedGraph S)
    (q : ConditionalQuery S) : Prop :=
  forall M : ExactModel S,
    Compatible M G -> 0 < (q.denominator M).num

def EventConditionalIdentifiable (G : ObservedGraph S)
    (q : ConditionalQuery S) : Prop :=
  forall (M N : ExactModel S),
    Compatible M G ->
    Compatible N G ->
    ObservationallyEquivalent M N ->
    0 < (q.denominator M).num ->
    0 < (q.denominator N).num ->
    q.ValueEquivalent M N

/-- Distributional identifiability is the notion used by the published theorem. -/
def Identifiable (G : ObservedGraph S) (q : JointKernelQuery S) : Prop :=
  forall (M N : ExactModel S),
    Compatible M G ->
    Compatible N G ->
    ObservationallyEquivalent M N ->
    q.ValueEquivalent M N

/--
A conditional kernel is identifiable when every pair of compatible,
observationally equivalent models agrees at each assignment supported by both
models.  This common-support notion does not require global support or equality
of support domains; `ConditionalKernelQuery.ResultEquivalent` expresses the
stronger full partial-result comparison.
-/
def ConditionalIdentifiable (G : ObservedGraph S)
    (q : ConditionalKernelQuery S) : Prop :=
  forall (M N : ExactModel S),
    Compatible M G ->
    Compatible N G ->
    ObservationallyEquivalent M N ->
    q.ValueEquivalent M N

/-- Full kernel identifiability entails every local fixed-event instance. -/
theorem kernel_identifiable_implies_event_identifiable
    (G : ObservedGraph S) (q : InterventionalQuery S)
    (kernelIdentifiable : Identifiable G q.kernelQuery) :
    EventIdentifiable G q := by
  intro left right leftCompatible rightCompatible observational
  have kernelEquivalent := kernelIdentifiable left right leftCompatible
    rightCompatible observational
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

/-- An explicit finite rational witness that a query is not identifiable. -/
structure Counterexample (G : ObservedGraph S) (q : JointKernelQuery S) where
  left : ExactModel S
  right : ExactModel S
  left_compatible : Compatible left G
  right_compatible : Compatible right G
  observationally_equal : ObservationallyEquivalent left right
  query_separated : Not (q.ValueEquivalent left right)

theorem Counterexample.not_identifiable (C : Counterexample G q) :
    Not (Identifiable G q) := by
  intro h
  exact C.query_separated
    (h C.left C.right C.left_compatible C.right_compatible
      C.observationally_equal)

/-! ## Finite c-components, c-forests, and hedges -/

inductive DirectedReachableBy (S : ObservedSignature)
    (edge : Fin S.count -> Fin S.count -> Prop) :
    Fin S.count -> Fin S.count -> Prop
  | refl (i) : DirectedReachableBy S edge i i
  | tail {i j k} :
      DirectedReachableBy S edge i j -> edge j k ->
        DirectedReachableBy S edge i k

inductive BidirectedConnectedWithin (G : ObservedGraph S) (nodes : NodeSet S) :
    Fin S.count -> Fin S.count -> Prop
  | refl {i} : nodes i = true -> BidirectedConnectedWithin G nodes i i
  | tail {i j k} :
      BidirectedConnectedWithin G nodes i j ->
      nodes k = true -> G.bidirected j k = true ->
      BidirectedConnectedWithin G nodes i k

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

structure CForest (G : ObservedGraph S)
    (nodes roots : NodeSet S) : Prop where
  component : BidirectedComponent G nodes
  at_most_one_child : AtMostOneDirectedChild G nodes
  roots_exact : forall i, roots i = true <-> IsRootIn G nodes i

/-- The finite hedge obstruction for an ordinary interventional query. -/
structure HedgeWitness (G : ObservedGraph S)
    (q : JointKernelQuery S) where
  large : NodeSet S
  small : NodeSet S
  roots : NodeSet S
  large_forest : CForest G large roots
  small_forest : CForest G small roots
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

theorem typeTheoretic_kernel_identifiable_implies_event
    (G : ObservedGraph S) (q : InterventionalQuery S)
    (kernelIdentifiable : TypeTheoreticIdentifiable G q.kernelQuery) :
    TypeTheoreticEventIdentifiable G q :=
  kernel_identifiable_implies_event_identifiable G q kernelIdentifiable

end Causality
end Thesis
