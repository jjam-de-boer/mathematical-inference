import Thesis.CausalTransport.DSeparationWitness
import Thesis.CausalTransport.ActivePathTransport
import Thesis.CausalTransport.ConditionalFailureExtraction

namespace Thesis
namespace Causality

universe u

variable {S : ObservedSignature.{u}}

/-!
# Actual back-door paths at irreducible conditional failures

Exhaustion of IDC's exchange search is more than the absence of a successful
rule-2 certificate.  For every conditioner still present, its negative graph
test supplies an active path to an outcome, given the actions and all other
conditioners.  Such paths are graph ingredients of the remaining conditional
countermodel construction; a failed joint numerator alone does not supply a
conditional countermodel.

This module constructs the path data, not merely its propositional existence.
The finite witness search supplies the list, the singleton endpoint identifies
the original conditioner, and path reversal gives the needed orientation.
The outgoing cut at that conditioner forces the first edge to point into it.
Restoring its outgoing edges preserves the same active path in the ordinary
incoming-cut action graph, by the common-DAG edge-inclusion theorem.

None of these steps assumes a countermodel, a chosen path, or an identifiable
conditioning denominator.  The universal conditional countermodel theorem
remains a separate semantic obligation after these graph data are available.
-/

open PathSpecification

/-- A concrete active back-door path for one remaining conditioner.  The
conditioning set is exactly IDC's rule-2 set, and the path lives in `G_bar(X)`.
`first` and `rest` expose its initial incoming edge as data for a subsequent
path induction.  Outcome/condition disjointness excludes a singleton path. -/
structure ConditionalBackdoorPath (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (node : Fin S.count) : Type where
  outcome : Fin S.count
  outcome_selected : query.outcome outcome = true
  path : ActivePath graph (GraphMutilation.bar query.action)
    (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton node)))
    (.observed node) (.observed outcome)
  first : SeparationNode S
  rest : List (SeparationNode S)
  nodes_eq : path.nodes = .observed node :: first :: rest
  first_incoming : graph.expandedMutilatedEdge (GraphMutilation.bar query.action)
    first (.observed node) = true

/-- Restoring the singleton outgoing cut changes neither the action's
incoming cut nor any original arrow.  Every retained expanded edge survives. -/
private theorem exchangeEdge_in_actionGraph (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (node : Fin S.count)
    (left right : SeparationNode S)
    (edge : graph.expandedMutilatedEdge
      (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) left right = true) :
    graph.expandedMutilatedEdge (GraphMutilation.bar query.action) left right = true := by
  cases left with
  | observed parent =>
      cases right with
      | observed child =>
          simp only [ObservedGraph.expandedMutilatedEdge, GraphMutilation.barUnderline,
            GraphMutilation.bar, NodeSet.empty, Bool.not_false, Bool.and_true,
            Bool.and_eq_true] at edge ⊢
          exact ⟨edge.1.1, edge.2⟩
      | latentPair first second => cases edge
  | latentPair first second => exact edge

/-- No arrow can leave the very conditioner whose outgoing edges the
singleton exchange test removes.  This includes observed-to-latent pairs. -/
private theorem exchangeEdge_from_conditioner_false (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (node : Fin S.count) (next : SeparationNode S) :
    graph.expandedMutilatedEdge
      (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
      (.observed node) next = false := by
  have selected : NodeSet.singleton node node = true :=
    (NodeSet.singleton_eq_true_iff node node).mpr rfl
  cases next with
  | observed child =>
      simp only [ObservedGraph.expandedMutilatedEdge, GraphMutilation.barUnderline,
        selected, Bool.not_true, Bool.and_false, Bool.false_and]
  | latentPair first second => rfl

/-- Inspect a certified outgoing-cut path to expose its first incoming edge.
The returned pair is selected by inspecting the actual vertex list.  This
shared decoder applies equally to a first-success or a normalized witness. -/
private def firstIncomingOfCutPath (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (node outcome : Fin S.count)
    (selected : query.condition node = true) (outcomeSelected : query.outcome outcome = true)
    (cutPath : ActivePath graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
      (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton node)))
      (.observed node) (.observed outcome)) :
    { data : SeparationNode S × List (SeparationNode S) //
      cutPath.nodes = .observed node :: data.1 :: data.2 ∧
      graph.expandedMutilatedEdge (GraphMutilation.bar query.action) data.1 (.observed node) = true } := by
  cases nodes : cutPath.nodes with
  | nil =>
      have starts := cutPath.starts
      rw [nodes] at starts
      cases starts
  | cons first tail =>
      have first_eq : first = .observed node := by
        simpa only [nodes, List.head?_cons, Option.some.injEq] using cutPath.starts
      subst first
      cases tail with
      | nil =>
          have same : node = outcome := by
            simpa only [nodes, List.getLast?_singleton, Option.some.injEq,
              SeparationNode.observed.injEq] using cutPath.finishes
          have conditionFalse := query.outcome_condition_disjoint node (same ▸ outcomeSelected)
          exact False.elim (Bool.false_ne_true (conditionFalse.symm.trans selected))
      | cons next rest =>
          have adjacent : Adjacent graph
              (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
              (.observed node) next := by
            have consecutive := cutPath.adjacent
            rw [nodes] at consecutive
            exact consecutive.1
          have incoming : graph.expandedMutilatedEdge
              (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
              next (.observed node) = true := by
            rcases adjacent with outgoing | incoming
            · rw [exchangeEdge_from_conditioner_false graph query node next] at outgoing
              cases outgoing
            · exact incoming
          exact ⟨(next, rest), rfl, exchangeEdge_in_actionGraph graph query node _ _ incoming⟩

/-- Restore a supplied certified outgoing-cut path as a conditional back-door
path.  Its exact list is retained definitionally.  The outgoing cut derives
the first incoming edge; outcome/condition disjointness excludes a singleton.
This adapter does not require that the supplied path was the first search result. -/
def ConditionalBackdoorPath.ofCutPath (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (node outcome : Fin S.count)
    (selected : query.condition node = true) (outcomeSelected : query.outcome outcome = true)
    (cutPath : ActivePath graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
      (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton node)))
      (.observed node) (.observed outcome)) : ConditionalBackdoorPath graph query node :=
  let data := firstIncomingOfCutPath graph query node outcome selected outcomeSelected cutPath
  {
    outcome := outcome
    outcome_selected := outcomeSelected
    path := cutPath.ofEdgeInclusion (exchangeEdge_in_actionGraph graph query node)
    first := data.val.1
    rest := data.val.2
    nodes_eq := data.property.1
    first_incoming := data.property.2
  }

/-- The adapter restores edges without changing the actual normalized list.
This equality is definitional, not another search or a path-existence theorem. -/
theorem ConditionalBackdoorPath.ofCutPath_nodes (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (node outcome : Fin S.count)
    (selected : query.condition node = true) (outcomeSelected : query.outcome outcome = true)
    (cutPath : ActivePath graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
      (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton node)))
      (.observed node) (.observed outcome)) :
    (ConditionalBackdoorPath.ofCutPath graph query node outcome selected outcomeSelected cutPath).path.nodes =
      cutPath.nodes := rfl

/-- A failed singleton exchange yields an actual back-door path for the
original conditional query.  All selection and path data are returned by
finite searches or by inspecting their lists; there is no choice elimination. -/
def ConditionalBackdoorPath.ofExchangeTestFalse (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S) (node : Fin S.count)
    (selected : query.condition node = true)
    (failed : conditionalExchangeTest graph query node = false) :
    ConditionalBackdoorPath graph query node := by
  let connection := activeConnectionOfDSeparatedFalse graph
    (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
    query.outcome (NodeSet.singleton node)
    (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton node))) failed
  have target_eq : connection.target = node :=
    (NodeSet.singleton_eq_true_iff node connection.target).mp connection.target_selected
  let cutPath : ActivePath graph
      (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
      (NodeSet.union query.action (NodeSet.diff query.condition (NodeSet.singleton node)))
      (.observed node) (.observed connection.source) := by
    simpa only [target_eq] using connection.path.reverse
  exact .ofCutPath graph query node connection.source selected connection.source_selected cutPath

/-- Uniformly construct a back-door path for every remaining conditioner
when IDC can perform no further singleton exchange. -/
def ConditionalBackdoorPath.ofNoExchange (graph : ObservedGraph S)
    (query : ConditionalKernelQuery S)
    (exhausted : conditionalExchangeStep? graph query = none)
    (node : Fin S.count) (selected : query.condition node = true) :
    ConditionalBackdoorPath graph query node :=
  ConditionalBackdoorPath.ofExchangeTestFalse graph query node selected
    (conditionalExchangeStep?_none_excludes_all graph query exhausted node selected)

/-- No action vertex occurs anywhere on the returned back-door path.
Actions are both incoming-cut and conditioned in the exact exchange test,
so they cannot be open noncolliders or activated colliders along this path. -/
theorem ConditionalBackdoorPath.action_false_of_mem
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {node : Fin S.count}
    (backdoor : ConditionalBackdoorPath graph query node) (actionNode : Fin S.count)
    (member : .observed actionNode ∈ backdoor.path.nodes) : query.action actionNode = false := by
  cases selected : query.action actionNode with
  | false => rfl
  | true =>
      have given : NodeSet.union query.action
          (NodeSet.diff query.condition (NodeSet.singleton node)) actionNode = true :=
        Bool.or_eq_true_iff.mpr (Or.inl selected)
      exact False.elim
        (backdoor.path.not_mem_of_conditioned_incomingCut actionNode selected given member)

/-- The existing arbitrary-depth failure provenance now exposes actual
back-door data at its extracted terminal.  The exchange trace, joint hedge,
and original-query semantic transport remain unchanged. -/
def ConditionalKernelFailure.backdoorPath
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    {fail : IdentificationFail S} (failure : ConditionalKernelFailure graph query fail)
    (node : Fin S.count) (selected : failure.terminal.condition node = true) :
    ConditionalBackdoorPath graph failure.terminal node :=
  ConditionalBackdoorPath.ofNoExchange graph failure.terminal failure.no_exchange node selected

/-- An exhausted source admits no nontrivial verified exchange trace.
This uses the trace's certificates, not evaluation of its proof-bearing data. -/
theorem ConditionalExchangeTrace.target_eq_of_no_exchange
    {graph : ObservedGraph S} {source target : ConditionalKernelQuery S}
    (trace : ConditionalExchangeTrace graph source target)
    (exhausted : conditionalExchangeStep? graph source = none) : target = source := by
  cases trace with
  | refl query => rfl
  | exchange step rest =>
      have excluded := conditionalExchangeStep?_none_excludes_all _ _ exhausted
        step.node step.selected
      exact False.elim (Bool.false_ne_true (excluded.symm.trans step.separated))

/-- Public failure extraction retains an irreducible input query literally. -/
theorem identifyConditionalKernelFailed_terminal_of_no_exchange
    {graph : ObservedGraph S} (query : ConditionalKernelQuery S)
    {fail : IdentificationFail S}
    (exhausted : conditionalExchangeStep? graph query = none)
    (result : identifyConditionalKernel graph query = .failed fail) :
    (identifyConditionalKernelFailed query result).terminal = query :=
  (identifyConditionalKernelFailed query result).exchanges.target_eq_of_no_exchange exhausted

end Causality
end Thesis
