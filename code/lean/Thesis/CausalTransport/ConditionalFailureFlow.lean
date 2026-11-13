import Thesis.CausalTransport.HedgeChannelFlowDirection
import Thesis.CausalTransport.HedgeChannelConditionalCounterexample
import Thesis.CausalTransport.ConditionalFailurePivot

namespace Thesis
namespace Causality

/-!
# Every original hedge supplies a conditional countermodel or a normalized pivot

The earlier latest-pivot construction obtains a reachable conditioner when
every composed flow sink is inspected.  This module removes that prerequisite
from the normalization branch.  It tests all forward-path vertices directly,
without assuming that endpoint omission alone proves their freedom; flipping
an outside-small sink alone does not supply a balance direction.

Here we inspect the *entire actual forward flow path* from the hedge's stored
action root.  If no conditioner occurs, the whole-path balance theorem makes
that root the sole odd local source and every outside-small row even.  The
existing complete-marginal theorem and original-label construction then
return a genuine positive conditional countermodel for the unchanged query.

Otherwise a finite list search returns an actual encountered conditioner.
Its prefix proves reachability from the same original small-forest source,
and the finite ordered construction returns a latest reachable pivot.  This
branch no longer requires that every flow sink be conditioned.

The result is an inspectable `Sum` of actual data, selected by a Boolean
finite-path test.  It does not decide semantic identifiability or choose a
countermodel from an existential proposition.  The latest-pivot branch still
needs the general path/forest parity argument; this reduction is not itself
an inhabitant of the full `PublishedCompleteness` interface.
-/

open Probability PathSpecification HedgeChannelInstallation

variable {S : ObservedSignature.{0}}

/-! ## A displayed path prefix proves actual incoming-cut reachability -/

/-- Every member of a directed list is reached from its displayed first
vertex.  Membership is used only to establish reachability in `Prop`; the
conditioner's actual data are returned separately by the finite list search. -/
private theorem reachable_of_consecutive_mem (edge : Fin S.count -> Fin S.count -> Bool)
    (nodes : List (Fin S.count)) (source : Fin S.count) (starts : nodes.head? = some source)
    (consecutive : Consecutive (fun parent child => edge parent child = true) nodes)
    (target : Fin S.count) (member : target ∈ nodes) : FiniteReachability.Reachable edge source target := by
  induction nodes generalizing source with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      have same : head = source := Option.some.inj starts
      subst head
      rcases List.mem_cons.mp member with equal | later
      · subst target
        exact FiniteReachability.Reachable.refl edge source
      · cases tail with
        | nil => cases later
        | cons next rest =>
            exact FiniteReachability.Reachable.prepend consecutive.1
              (inductionHypothesis next rfl consecutive.2 later)

/-! ## The witness's actual composed source flow -/

/-- Follow the original action root through the composed small/outcome map.
That source already belongs to Small; no source vertex or forward path is
chosen from the hedge's propositional forest fields. -/
def HedgeWitness.sourceOutcomeFlowPath
    {graph : ObservedGraph S} {query : JointKernelQuery S} (w : HedgeWitness graph query) :
    SuccessorPath w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor w.actionRoot :=
  SuccessorPath.ofForest w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
    w.smallOutcomeFlowSuccessor_wellFormed w.actionRoot
    (outcomeFlow_small_subset w w.actionRoot w.actionRoot_in_small)

/-- A returned path member is genuinely reachable from the stored hedge
source under the full original action cut.  Kept-map well-formedness and
domain avoidance justify every displayed edge; no added edge is used. -/
private theorem sourceOutcomeFlowPath_reachable_member
    {graph : ObservedGraph S} {query : JointKernelQuery S} (w : HedgeWitness graph query)
    (node : Fin S.count) (member : node ∈ w.sourceOutcomeFlowPath.nodes) :
    FiniteReachability.within finBeq (NodeSet.enumerated S)
      (mutilatedDirected S query.action) S.count w.actionRoot node = true := by
  have actualEdges : Consecutive (fun parent child => mutilatedDirected S query.action parent child = true)
      w.sourceOutcomeFlowPath.nodes := by
    apply Consecutive.mono _ _ w.sourceOutcomeFlowPath.consecutive
    intro parent child next
    have parts := childWellFormed_edge w.smallOutcomeFlowNodes w.smallOutcomeFlowSuccessor
      w.smallOutcomeFlowSuccessor_wellFormed next
    have free := outcomeFlow_avoids_action w child parts.2.1
    simp only [mutilatedDirected, free, Bool.false_eq_true, if_false]
    exact parts.2.2
  have reachable := reachable_of_consecutive_mem (mutilatedDirected S query.action)
    w.sourceOutcomeFlowPath.nodes w.actionRoot w.sourceOutcomeFlowPath.starts actualEdges node member
  have bounded := FiniteReachability.boundedWalk_of_reachable finBeq (NodeSet.enumerated S)
    (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) reachable
  rw [NodeSet.length_enumerated] at bounded
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
    (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mpr bounded

/-! ## The exhaustive finite flow split -/

/-- Every supplied original-numerator hedge gives either a positive
original-conditional countermodel or a latest reachable conditioning pivot.

The left branch is fully semantic: the entire conditioning marginal is equal
in the same original-alphabet model pair whose numerator is separated.  The
right branch retains the original query and the same stored hedge source,
without an all-sinks-inspected, singleton-root, path-avoidance, or guessed
denominator premise.  At an irreducible terminal its pivot also has the actual
back-door path and collider-activation normalization proved earlier. -/
noncomputable def HedgeWitness.conditionalCounterexampleOrLatestPivot
    {graph : ObservedGraph S} {query : ConditionalKernelQuery S}
    (w : HedgeWitness graph query.jointNumerator) (rich : ObservedSignature.ValueRich S) :
    Sum (ConditionalCounterexampleIn (GraphModelClass.positive graph) query)
      (LatestConditionalPivot graph query w.actionRoot) := by
  cases encountered : w.sourceOutcomeFlowPath.nodes.any query.condition with
  | false =>
      have free : forall node, node ∈ w.sourceOutcomeFlowPath.nodes -> query.condition node = false := by
        intro node member
        cases selected : query.condition node with
        | false => rfl
        | true =>
            have found : w.sourceOutcomeFlowPath.nodes.any query.condition = true :=
              List.any_eq_true.mpr ⟨node, member, selected⟩
            exact False.elim (Bool.false_ne_true (encountered.symm.trans found))
      let direction := OutcomeFlowBalanceDirection.ofPath w query.condition w.actionRoot
        w.actionRoot_in_small w.sourceOutcomeFlowPath free
      exact .inl (conditionalCounterexampleOfBalanceDirection query w rich direction)
  | true =>
      let conditioner := listFirstAny w.sourceOutcomeFlowPath.nodes query.condition encountered
      have selected := listFirstAny_pred w.sourceOutcomeFlowPath.nodes query.condition encountered
      have member := listFirstAny_mem w.sourceOutcomeFlowPath.nodes query.condition encountered
      have reachable := sourceOutcomeFlowPath_reachable_member w conditioner member
      exact .inr (LatestConditionalPivot.ofReachableConditioner graph query w.actionRoot
        conditioner selected reachable)

end Causality
end Thesis
