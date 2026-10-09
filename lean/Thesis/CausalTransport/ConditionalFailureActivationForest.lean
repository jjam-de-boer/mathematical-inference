import Thesis.CausalTransport.ConditionalFailurePivot
import Thesis.CausalTransport.HedgeChannelFlowDirection

namespace Thesis
namespace Causality

open PathSpecification HedgeChannelInstallation

/-!
# One consistent successor policy for all collider activations

Independent activation paths can meet.  Installing their edges separately
would then leave competing successors at a shared vertex, or count its local
row more than once.  Here a single finite directed forest supplies a common
policy for every observed vertex which can reach another conditioner.

Its domain is computed in the original incoming-cut action graph.  Every
selected unconditioned vertex keeps the earliest declared child which remains
in that domain, and every selected conditioner stops.  Reachability proves
that a nonconditioned selected vertex really has such a child.  Strict graph
order supplies termination; arbitrary merging parents are allowed.

For a latest reachable pivot, the entire domain avoids that pivot.  Otherwise
a different conditioner would be both reachable from the same hedge source
and later than the pivot.  Each actual collider activation therefore has a
complete path under this common policy, with only its final vertex conditioned.
In particular two paths which meet cannot choose different outgoing edges.

This domain is an auxiliary routing domain, not a declaration that every one
of its rows must be selected in a countermodel interaction.  It may contain
irrelevant ancestors.  Later parity construction must decide which portions
to use, and must still handle intersections with the active path and the
mandatory small-forest rows.  No such disjointness is assumed or proved here.
-/

variable {S : ObservedSignature.{0}}

/-! ## Executable reachability domain and its common successor -/

private def activationTargets (query : ConditionalKernelQuery S) (pivot : Fin S.count) : NodeSet S :=
  NodeSet.diff query.condition (NodeSet.singleton pivot)

private def activationReach (query : ConditionalKernelQuery S) (source target : Fin S.count) : Bool :=
  FiniteReachability.within finBeq (NodeSet.enumerated S)
    (mutilatedDirected S query.action) S.count source target

private def activationNodes (query : ConditionalKernelQuery S) (pivot : Fin S.count) : NodeSet S :=
  fun node => !query.action node &&
    (NodeSet.members (activationTargets query pivot)).any (activationReach query node)

private def activationSuccessor (query : ConditionalKernelQuery S) (pivot : Fin S.count) : ForestChild S :=
  fun parent => if activationNodes query pivot parent && !query.condition parent then
    (directedChildren (activationNodes query pivot) parent).head?
  else none

private theorem activationReach_of_reachable (query : ConditionalKernelQuery S)
    (source target : Fin S.count)
    (reachable : FiniteReachability.Reachable (mutilatedDirected S query.action) source target) :
    activationReach query source target = true := by
  have bounded := FiniteReachability.boundedWalk_of_reachable finBeq (NodeSet.enumerated S)
    (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) reachable
  rw [NodeSet.length_enumerated] at bounded
  exact (FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
    (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mpr bounded

private theorem reachable_of_activationReach (query : ConditionalKernelQuery S)
    (source target : Fin S.count) (reaches : activationReach query source target = true) :
    FiniteReachability.Reachable (mutilatedDirected S query.action) source target :=
  FiniteReachability.Reachable.of_bounded
    ((FiniteReachability.within_eq_true_iff_boundedWalk finBeq (NodeSet.enumerated S)
      (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) _ _ _).mp reaches)

/-- Only existence in `Prop` is extracted from a walk.  The actual successor
data are still obtained by the executable ordered child list below. -/
private theorem first_edge_of_reachable (query : ConditionalKernelQuery S)
    (source target : Fin S.count) (different : source ≠ target)
    (reachable : FiniteReachability.Reachable (mutilatedDirected S query.action) source target) :
    Exists fun child => mutilatedDirected S query.action source child = true ∧
      FiniteReachability.Reachable (mutilatedDirected S query.action) child target := by
  rcases reachable with ⟨length, ⟨walk⟩⟩
  cases walk with
  | refl => exact False.elim (different rfl)
  | @step length source child target edge rest => exact ⟨child, edge, ⟨length, ⟨rest⟩⟩⟩

private theorem activationNodes_action_free (query : ConditionalKernelQuery S)
    (pivot node : Fin S.count) (selected : activationNodes query pivot node = true) :
    query.action node = false := by
  simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp selected).1

private theorem target_parts (query : ConditionalKernelQuery S) (pivot target : Fin S.count)
    (selected : activationTargets query pivot target = true) :
    query.condition target = true ∧ target ≠ pivot := by
  have parts := Bool.and_eq_true_iff.mp selected
  refine ⟨parts.1, ?_⟩
  intro same
  subst target
  have present := (NodeSet.singleton_eq_true_iff pivot pivot).mpr rfl
  rw [present] at parts
  cases parts.2

/-- An unconditioned ancestor has a declared child in the same computed
domain.  The incoming cut derives the child's action freedom automatically. -/
private theorem activation_child_exists (query : ConditionalKernelQuery S)
    (pivot parent : Fin S.count) (selected : activationNodes query pivot parent = true)
    (unconditioned : query.condition parent = false) :
    Exists fun child => child ∈ directedChildren (activationNodes query pivot) parent := by
  rcases List.any_eq_true.mp (Bool.and_eq_true_iff.mp selected).2 with ⟨target, member, reaches⟩
  have targetSelected := (NodeSet.mem_members_iff (activationTargets query pivot) target).mp member
  have conditionTarget := (target_parts query pivot target targetSelected).1
  have different : parent ≠ target := by
    intro same
    subst target
    exact Bool.false_ne_true (unconditioned.symm.trans conditionTarget)
  rcases first_edge_of_reachable query parent target different
    (reachable_of_activationReach query parent target reaches) with ⟨child, edge, rest⟩
  have childFree := action_false_of_mutilatedDirected query.action edge
  have actual : S.directed parent child = true ∧ query.action child = false := by
    refine ⟨?_, childFree⟩
    simpa only [mutilatedDirected, childFree, Bool.false_eq_true, if_false] using edge
  have freeBit : Bool.not (query.action child) = true := by simp only [actual.2, Bool.not_false]
  have childSelected : activationNodes query pivot child = true :=
    Bool.and_eq_true_iff.mpr ⟨freeBit,
      List.any_eq_true.mpr ⟨target, member, activationReach_of_reachable query child target rest⟩⟩
  exact ⟨child, (mem_directedChildren_iff (activationNodes query pivot) parent child).mpr ⟨childSelected, actual.1⟩⟩

private theorem activationSuccessor_condition_none (query : ConditionalKernelQuery S)
    (pivot node : Fin S.count) (conditioned : query.condition node = true) :
    activationSuccessor query pivot node = none := by
  simp only [activationSuccessor, conditioned, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]

private theorem activationSuccessor_none_condition (query : ConditionalKernelQuery S)
    (pivot node : Fin S.count) (selected : activationNodes query pivot node = true)
    (stopped : activationSuccessor query pivot node = none) : query.condition node = true := by
  cases conditioned : query.condition node with
  | true => rfl
  | false =>
      rcases activation_child_exists query pivot node selected conditioned with ⟨child, member⟩
      cases children : directedChildren (activationNodes query pivot) node with
      | nil => rw [children] at member; cases member
      | cons head tail =>
          simp only [activationSuccessor, selected, conditioned, Bool.not_false, Bool.and_self, if_true,
            children, List.head?_cons] at stopped
          cases stopped

private theorem activationSuccessor_wellFormed (query : ConditionalKernelQuery S) (pivot : Fin S.count) :
    childWellFormedBool (activationNodes query pivot) (activationSuccessor query pivot) = true := by
  apply List.all_eq_true.mpr
  intro parent _member
  cases selected : activationNodes query pivot parent with
  | false => simp only [activationSuccessor, selected, Bool.false_and, Bool.false_eq_true, if_false]
  | true =>
      cases conditioned : query.condition parent with
      | true => rw [activationSuccessor_condition_none query pivot parent conditioned]
      | false =>
          cases children : directedChildren (activationNodes query pivot) parent with
          | nil => simp only [activationSuccessor, selected, conditioned, Bool.not_false, Bool.and_self, if_true,
              children, List.head?_nil]
          | cons child rest =>
              have member : child ∈ directedChildren (activationNodes query pivot) parent := by
                rw [children]
                exact List.mem_cons_self
              have parts := (mem_directedChildren_iff (activationNodes query pivot) parent child).mp member
              simp only [activationSuccessor, selected, conditioned, Bool.not_false, Bool.and_self, if_true,
                children, List.head?_cons, parts.1, parts.2, Bool.and_self]

/-- Topological order applies to any actual observed reachability witness.
The eliminations stay in `Prop`, with no maximizer or path chosen from it. -/
private theorem reachable_order (query : ConditionalKernelQuery S)
    (source target : Fin S.count)
    (reachable : FiniteReachability.Reachable (mutilatedDirected S query.action) source target) :
    source.val ≤ target.val := by
  rcases reachable with ⟨length, ⟨walk⟩⟩
  induction walk with
  | refl => exact Nat.le_refl _
  | step edge _rest inductionHypothesis =>
      exact Nat.le_trans (Nat.le_of_lt (mutilatedDirected_earlier S query.action edge)) inductionHypothesis

private theorem activationNodes_pivot_free {graph : ObservedGraph S}
    {query : ConditionalKernelQuery S} {source : Fin S.count}
    (pivot : LatestConditionalPivot graph query source) : activationNodes query pivot.node pivot.node = false := by
  cases selected : activationNodes query pivot.node pivot.node with
  | false => rfl
  | true =>
      rcases List.any_eq_true.mp (Bool.and_eq_true_iff.mp selected).2 with ⟨target, member, reaches⟩
      have targetSelected := (NodeSet.mem_members_iff (activationTargets query pivot.node) target).mp member
      have parts := target_parts query pivot.node target targetSelected
      have rest := reachable_of_activationReach query pivot.node target reaches
      have initial := reachable_of_activationReach query source pivot.node pivot.reachable
      have initialBounded := FiniteReachability.boundedWalk_of_reachable finBeq (NodeSet.enumerated S)
        (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) initial
      have restBounded := FiniteReachability.boundedWalk_of_reachable finBeq (NodeSet.enumerated S)
        (mutilatedDirected S query.action) finBeq_eq_true_iff (NodeSet.mem_enumerated S) rest
      have combined := activationReach_of_reachable query source target
        (FiniteReachability.Reachable.of_bounded (initialBounded.trans restBounded))
      have latest := pivot.latest target parts.1 combined
      have ordered := reachable_order query pivot.node target rest
      have same : target = pivot.node := Fin.ext (Nat.le_antisymm latest ordered)
      exact False.elim (parts.2 same)

/-! ## A common forest, not a family of independently installed branches -/

/-- A directed routing policy for every supplied collider activation.
The entire domain avoids the action and omitted pivot; conditioned vertices
are exactly its sinks.  Multiple incoming branches may meet at one vertex.
The domain is not itself a chosen background-interaction selection. -/
structure ConditionalColliderActivationForest (query : ConditionalKernelQuery S) (pivot : Fin S.count) where
  nodes : NodeSet S
  successor : ForestChild S
  wellFormed : childWellFormedBool nodes successor = true
  action_free : forall node, nodes node = true -> query.action node = false
  pivot_free : nodes pivot = false
  sink_iff_condition : forall node, nodes node = true -> (successor node = none ↔ query.condition node = true)
  contains_activation : forall collider, ConditionalColliderActivationRoute query pivot collider -> nodes collider = true

namespace ConditionalColliderActivationForest

variable {query : ConditionalKernelQuery S} {pivot : Fin S.count}

/-- Construct the common finite policy from a latest reachable pivot.
No disjoint-branch, unique-incoming-parent, or forest-intersection hypothesis
is supplied.  Actual child data come from the ordered finite child list. -/
def ofLatestPivot {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {source : Fin S.count}
    (pivot : LatestConditionalPivot graph query source) : ConditionalColliderActivationForest query pivot.node where
  nodes := activationNodes query pivot.node
  successor := activationSuccessor query pivot.node
  wellFormed := activationSuccessor_wellFormed query pivot.node
  action_free := activationNodes_action_free query pivot.node
  pivot_free := activationNodes_pivot_free pivot
  sink_iff_condition := fun node selected =>
    ⟨activationSuccessor_none_condition query pivot.node node selected,
      activationSuccessor_condition_none query pivot.node node⟩
  contains_activation := by
    intro collider route
    have starts := route.starts
    have member : collider ∈ route.before ++ [route.endpoint] := List.mem_of_head? starts
    have finishes : (route.before ++ [route.endpoint]).getLast? = some route.endpoint := by
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
    have reaches := activationReach_of_reachable query collider route.endpoint
      (FiniteReachability.Reachable.of_consecutive _ _ starts finishes route.consecutive)
    have targetSelected : activationTargets query pivot.node route.endpoint = true := by
      have absent : NodeSet.singleton pivot.node route.endpoint = false := by
        apply decide_eq_false
        exact route.endpoint_ne_pivot
      apply Bool.and_eq_true_iff.mpr
      refine ⟨route.endpoint_condition, ?_⟩
      change Bool.not (NodeSet.singleton pivot.node route.endpoint) = true
      rw [absent]
      rfl
    have freeBit : Bool.not (query.action collider) = true := by
      simp only [route.action_free collider member, Bool.not_false]
    exact Bool.and_eq_true_iff.mpr ⟨freeBit,
      List.any_eq_true.mpr ⟨route.endpoint, (NodeSet.mem_members_iff _ _).mpr targetSelected, reaches⟩⟩

/-- The common policy returns a complete path for any selected collider.
Once two such paths meet, their later steps consult the same successor map;
no second installation at the shared child is needed. -/
def path (forest : ConditionalColliderActivationForest query pivot)
    (collider : Fin S.count) (selected : forest.nodes collider = true) :
    SuccessorPath forest.nodes forest.successor collider :=
  .ofForest forest.nodes forest.successor forest.wellFormed collider selected

/-- Every actual collider window of a conditional back-door path is covered
by the same routing policy.  Its activity supplies the activation route, and
the forest's proved coverage supplies the domain membership.  No independent
activation or selected-collider flag is requested from the caller. -/
def pathOfBackdoorCollider {graph : ObservedGraph S}
    (forest : ConditionalColliderActivationForest query pivot)
    (backdoor : ConditionalBackdoorPath graph query pivot)
    (before after : List (SeparationNode S)) (previous next : SeparationNode S)
    (collider : Fin S.count)
    (window : backdoor.path.nodes = before ++ previous :: .observed collider :: next :: after)
    (isCollider : IsCollider graph (GraphMutilation.bar query.action) previous (.observed collider) next) :
    SuccessorPath forest.nodes forest.successor collider :=
  forest.path collider (forest.contains_activation collider
    (backdoor.colliderActivationRoute before after previous next collider window isCollider))

/-- The actual complete path stops at a remaining conditioner other than
the omitted pivot.  The sink fact is derived from the common policy. -/
theorem path_endpoint_condition (forest : ConditionalColliderActivationForest query pivot)
    (collider : Fin S.count) (selected : forest.nodes collider = true) :
    query.condition (forest.path collider selected).endpoint = true ∧
      (forest.path collider selected).endpoint ≠ pivot := by
  let route := forest.path collider selected
  have member : route.endpoint ∈ route.nodes := List.mem_of_getLast? route.finishes
  have inside := route.inside route.endpoint member
  refine ⟨(forest.sink_iff_condition route.endpoint inside).mp route.stopped, ?_⟩
  intro same
  rw [same, forest.pivot_free] at inside
  cases inside

/-- Only the final vertex may be conditioned.  If an earlier vertex were
conditioned, its actual successor would be `none`, contradicting the next
displayed step of the complete simple path. -/
theorem path_before_condition_free (forest : ConditionalColliderActivationForest query pivot)
    (collider : Fin S.count) (selected : forest.nodes collider = true)
    (node : Fin S.count) (member : node ∈ (forest.path collider selected).nodes)
    (notEndpoint : node ≠ (forest.path collider selected).endpoint) : query.condition node = false := by
  let route := forest.path collider selected
  have notLast : route.nodes.getLast? ≠ some node := by
    intro same
    exact notEndpoint (Option.some.inj (same.symm.trans route.finishes))
  have found := routeSuccessor_isSome_of_mem_of_not_last route.nodes node route.simple member notLast
  cases next : routeSuccessor route.nodes node with
  | none => rw [next] at found; cases found
  | some child =>
      have edge := routeSuccessor_rel_of_eq_some (fun parent child => forest.successor parent = some child)
        route.nodes node child route.consecutive next
      cases conditioned : query.condition node with
      | false => rfl
      | true =>
          have stopped := (forest.sink_iff_condition node (route.inside node member)).mpr conditioned
          change forest.successor node = some child at edge
          rw [stopped] at edge
          cases edge

/-- Arbitrary merging activation paths reach the same actual conditioned
sink.  This is the complete-path determinism theorem, not a uniqueness
assumption about declared incoming graph parents. -/
theorem path_endpoints_eq_of_shared (forest : ConditionalColliderActivationForest query pivot)
    (left right : Fin S.count) (leftSelected : forest.nodes left = true) (rightSelected : forest.nodes right = true)
    (shared : Fin S.count) (leftMember : shared ∈ (forest.path left leftSelected).nodes)
    (rightMember : shared ∈ (forest.path right rightSelected).nodes) :
    (forest.path left leftSelected).endpoint = (forest.path right rightSelected).endpoint :=
  (forest.path left leftSelected).endpoint_eq_of_shared (forest.path right rightSelected) shared leftMember rightMember

end ConditionalColliderActivationForest

end Causality
end Thesis
