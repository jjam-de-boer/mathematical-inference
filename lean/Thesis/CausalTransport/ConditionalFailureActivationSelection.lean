import Thesis.CausalTransport.ConditionalFailureActivationAvoidance
import Thesis.CausalTransport.ActivePathBoundary

namespace Thesis
namespace Causality

open PathSpecification HedgeChannelInstallation

variable {S : ObservedSignature.{0}}

/-!
# Select the actual collider traces, not every activation ancestor

The common activation policy has a deliberately generous auxiliary domain.
It can include noncolliders on the normalized path, even though each actual
collider's complete trace meets that path only at its own source.  Consequently
the whole auxiliary domain is not a sound interaction-row selection.

The shared `ActivePathBoundary` window scan finds exactly the observed
internal colliders of the normal form.  Phase balance and activation selection
therefore use the same executable collider mask.  A second finite scan takes
the union of their complete common-policy traces.  This union is
successor-closed, so restricting the policy to it preserves every selected
trace and its genuinely conditioned
endpoint.  Branches may merge: a Boolean union retains a shared vertex once,
and the common successor retains one outgoing map there.

The selected union may also meet the mandatory small hedge forest.  Its
outside-small portion is therefore a difference, not another copy of the
whole activation union.  The partition below retains the inside-small part
explicitly.  It does not assert small-forest disjointness, choose an odd
direction, or prove the remaining combined path/forest parity conservation.
-/

/-! ## The finite scan has exactly the displayed collider windows -/

namespace ConditionalBackdoorPathNormalForm

/-- The actual observed internal collider sources of this exact cut path.
Endpoints are not scanned as collider windows, and no latent vertex can
silently be used as an observed activation source. -/
def colliderSeeds {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {node : Fin S.count}
    (normal : ConditionalBackdoorPathNormalForm graph query node) : NodeSet S :=
  ActivePathInput.colliderRows graph
    (GraphMutilation.barUnderline query.action (NodeSet.singleton node)) normal.cutPath.nodes

/-- Every selected source is tied to an actual internal window of the
same normal form, and every such collider is selected.  The existential
window is used only in proofs; the source mask itself is the finite scan. -/
theorem colliderSeeds_eq_true_iff {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {node : Fin S.count}
    (normal : ConditionalBackdoorPathNormalForm graph query node) (collider : Fin S.count) :
    normal.colliderSeeds collider = true ↔
      Exists fun before : List (SeparationNode S) => Exists fun after : List (SeparationNode S) =>
        Exists fun previous : SeparationNode S => Exists fun next : SeparationNode S =>
          normal.cutPath.nodes = before ++ previous :: .observed collider :: next :: after ∧
            IsCollider graph (GraphMutilation.barUnderline query.action (NodeSet.singleton node))
              previous (.observed collider) next :=
  ActivePathInput.colliderRows_eq_true_iff graph _ collider normal.cutPath.nodes

variable {graph : ObservedGraph S} {query : ConditionalKernelQuery S} {source : Fin S.count}
    (pivot : LatestConditionalPivot graph query source)
    (normal : ConditionalBackdoorPathNormalForm graph query pivot.node)
    (forest : ConditionalColliderActivationForest query pivot.node)

/-- Activity and coverage derive domain membership for every scanned
collider.  No second selected-collider flag is needed by the trace union. -/
theorem colliderSeeds_in_forest (collider : Fin S.count) (selected : normal.colliderSeeds collider = true) :
    forest.nodes collider = true := by
  rcases (normal.colliderSeeds_eq_true_iff collider).mp selected with ⟨before, after, previous, next, window, actual⟩
  let path := normal.activationForestPath pivot forest before after previous next collider window actual
  exact path.inside collider (List.mem_of_head? path.starts)

/-- Union of the complete traces from the actual collider sources.
Proof-bearing member entries certify coverage, but all returned list and
mask data come from finite scans and the already executable common policy. -/
def activationTraceNodes : NodeSet S := fun node =>
  (NodeSet.members normal.colliderSeeds).attach.any (fun seed =>
    decide (node ∈ (forest.path seed.val (normal.colliderSeeds_in_forest pivot forest seed.val
      ((NodeSet.mem_members_iff _ _).mp seed.property))).nodes))

private theorem activationTraceNodes_eq_true_iff (node : Fin S.count) :
    normal.activationTraceNodes pivot forest node = true ↔
      Exists fun collider : Fin S.count => Exists fun selected : normal.colliderSeeds collider = true =>
        node ∈ (forest.path collider (normal.colliderSeeds_in_forest pivot forest collider selected)).nodes := by
  unfold activationTraceNodes
  rw [List.any_eq_true]
  constructor
  · rintro ⟨seed, _member, visited⟩
    exact ⟨seed.val, (NodeSet.mem_members_iff _ _).mp seed.property, of_decide_eq_true visited⟩
  · rintro ⟨collider, selected, visited⟩
    let seed : { collider // collider ∈ NodeSet.members normal.colliderSeeds } :=
      ⟨collider, (NodeSet.mem_members_iff _ _).mpr selected⟩
    exact ⟨seed, List.mem_attach _ _, decide_eq_true visited⟩

/-- Every row in the pruned trace union belongs to the original policy
domain; irrelevant auxiliary ancestors need not be included in the union. -/
theorem activationTraceNodes_subset_forest : NodeSet.Subset (normal.activationTraceNodes pivot forest) forest.nodes := by
  intro node selected
  rcases (normal.activationTraceNodes_eq_true_iff pivot forest node).mp selected with ⟨collider, seed, visited⟩
  exact (forest.path collider (normal.colliderSeeds_in_forest pivot forest collider seed)).inside node visited

/-- Pruning inherits full original-action avoidance from the actual
policy domain, rather than merely avoiding the stored intervention seed. -/
theorem activationTraceNodes_action_free (node : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest node = true) : query.action node = false :=
  forest.action_free node (normal.activationTraceNodes_subset_forest pivot forest node selected)

/-- The omitted latest pivot remains absent from the pruned union. -/
theorem activationTraceNodes_pivot_free : normal.activationTraceNodes pivot forest pivot.node = false := by
  cases selected : normal.activationTraceNodes pivot forest pivot.node with
  | false => rfl
  | true =>
      have inside := normal.activationTraceNodes_subset_forest pivot forest pivot.node selected
      rw [forest.pivot_free] at inside
      cases inside

/-- The whole complete trace of every actual collider is retained, not
just its endpoint or a prefix before its first Small intersection. -/
theorem activationTraceNodes_contains_path (collider : Fin S.count) (selected : normal.colliderSeeds collider = true)
    (node : Fin S.count)
    (visited : node ∈ (forest.path collider (normal.colliderSeeds_in_forest pivot forest collider selected)).nodes) :
    normal.activationTraceNodes pivot forest node = true :=
  (normal.activationTraceNodes_eq_true_iff pivot forest node).mpr ⟨collider, selected, visited⟩

/-- All actual collider sources, including already-conditioned zero-edge
sources, belong to their own complete trace union. -/
theorem colliderSeeds_subset_activationTraceNodes :
    NodeSet.Subset normal.colliderSeeds (normal.activationTraceNodes pivot forest) := by
  intro collider selected
  exact normal.activationTraceNodes_contains_path pivot forest collider selected collider
    (List.mem_of_head? (forest.path collider (normal.colliderSeeds_in_forest pivot forest collider selected)).starts)

/-! ## Successor closure preserves the complete original traces -/

private theorem successor_path_closed {domain : NodeSet S} {successor : ForestChild S} {start : Fin S.count}
    (path : SuccessorPath domain successor start) (parent child : Fin S.count)
    (visited : parent ∈ path.nodes) (edge : successor parent = some child) : child ∈ path.nodes := by
  have notLast : path.nodes.getLast? ≠ some parent := by
    intro last
    have same : path.endpoint = parent := Option.some.inj (path.finishes.symm.trans last)
    have stopped := path.stopped
    rw [same, edge] at stopped
    cases stopped
  have found := routeSuccessor_isSome_of_mem_of_not_last path.nodes parent path.simple visited notLast
  cases next : routeSuccessor path.nodes parent with
  | none => rw [next] at found; cases found
  | some actual =>
      have actualEdge := routeSuccessor_rel_of_eq_some (fun parent child => successor parent = some child)
        path.nodes parent actual path.consecutive next
      have same : actual = child := Option.some.inj (actualEdge.symm.trans edge)
      exact same ▸ (routeSuccessor_mem path.nodes parent actual next).2

/-- A selected transmitter's actual successor stays in the selected
union.  This includes shared suffixes after arbitrary branch merges. -/
theorem activationTraceNodes_successor_closed (parent child : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest parent = true) (edge : forest.successor parent = some child) :
    normal.activationTraceNodes pivot forest child = true := by
  rcases (normal.activationTraceNodes_eq_true_iff pivot forest parent).mp selected with ⟨collider, seed, visited⟩
  apply normal.activationTraceNodes_contains_path pivot forest collider seed child
  exact successor_path_closed _ parent child visited edge

/-- Prune only the transmitting domain; a selected conditioned sink keeps
`none`, rather than falling through to an unrelated successor map. -/
def activationTraceSuccessor : ForestChild S := restrictChild (normal.activationTraceNodes pivot forest) forest.successor

/-- The restricted map is well formed on the pruned domain itself.  The
closure proof above is essential: restricting only the source mask of an
arbitrary subset would not justify destination membership in that subset. -/
theorem activationTraceSuccessor_wellFormed :
    childWellFormedBool (normal.activationTraceNodes pivot forest) (normal.activationTraceSuccessor pivot forest) = true := by
  apply List.all_eq_true.mpr
  intro parent _member
  cases selected : normal.activationTraceNodes pivot forest parent with
  | false => simp only [activationTraceSuccessor, restrictChild, selected, Bool.false_eq_true, if_false]
  | true =>
      cases next : forest.successor parent with
      | none => simp only [activationTraceSuccessor, restrictChild, selected, if_true, next]
      | some child =>
          have kept := normal.activationTraceNodes_successor_closed pivot forest parent child selected next
          have actual := (childWellFormed_edge forest.nodes forest.successor forest.wellFormed next).2.2
          simp only [activationTraceSuccessor, restrictChild, selected, if_true, next, kept, actual, Bool.and_self]

-- Replaying an already selected list changes only its successor certificates.
-- Each transmitting parent belongs to the mask, so no actual edge is lost.
private theorem consecutive_restrict (nodes : NodeSet S) (successor : ForestChild S) :
    forall route : List (Fin S.count),
      Consecutive (fun parent child => successor parent = some child) route ->
      (forall node, node ∈ route -> nodes node = true) ->
      Consecutive (fun parent child => restrictChild nodes successor parent = some child) route
  | [], _, _ => True.intro
  | [_], _, _ => True.intro
  | parent :: child :: rest, directed, inside =>
      ⟨(restrictChild_of_true (inside parent (List.mem_cons.mpr (Or.inl rfl)))).trans directed.1,
        consecutive_restrict nodes successor (child :: rest) directed.2
          (fun node member => inside node (List.mem_cons.mpr (Or.inr member)))⟩

/-- Repackage a collider's exact complete trace in the pruned domain.
The list and endpoint are unchanged; only domain/map certificates change.
No independent branch selection or replacement path search is performed. -/
def activationTracePath (collider : Fin S.count) (selected : normal.colliderSeeds collider = true) :
    SuccessorPath (normal.activationTraceNodes pivot forest) (normal.activationTraceSuccessor pivot forest) collider := by
  let path := forest.path collider (normal.colliderSeeds_in_forest pivot forest collider selected)
  refine {
    nodes := path.nodes
    endpoint := path.endpoint
    starts := path.starts
    finishes := path.finishes
    simple := path.simple
    consecutive := ?_
    stopped := ?_
    inside := normal.activationTraceNodes_contains_path pivot forest collider selected
  }
  · exact consecutive_restrict (normal.activationTraceNodes pivot forest) forest.successor path.nodes path.consecutive
      (normal.activationTraceNodes_contains_path pivot forest collider selected)
  · change restrictChild (normal.activationTraceNodes pivot forest) forest.successor path.endpoint = none
    rw [restrictChild_of_true (normal.activationTraceNodes_contains_path pivot forest collider selected path.endpoint
      (List.mem_of_getLast? path.finishes))]
    exact path.stopped

/-- Pruning retains the original complete list, including its actual
conditioned endpoint and every shared suffix vertex. -/
theorem activationTracePath_nodes (collider : Fin S.count) (selected : normal.colliderSeeds collider = true) :
    (normal.activationTracePath pivot forest collider selected).nodes =
      (forest.path collider (normal.colliderSeeds_in_forest pivot forest collider selected)).nodes := rfl

/-- The restricted policy stops precisely at selected conditioners.
Neither pruning nor a later overlap with Small may resume a conditioned sink. -/
theorem activationTraceSuccessor_sink_iff_condition (node : Fin S.count)
    (selected : normal.activationTraceNodes pivot forest node = true) :
    normal.activationTraceSuccessor pivot forest node = none ↔ query.condition node = true := by
  change restrictChild (normal.activationTraceNodes pivot forest) forest.successor node = none ↔ _
  rw [restrictChild_of_true selected]
  exact forest.sink_iff_condition node (normal.activationTraceNodes_subset_forest pivot forest node selected)

/-- The union intersects the normalized path exactly in its observed
internal collider sources.  The reverse implication is real source coverage,
not a domain-wide claim about the auxiliary activation forest. -/
theorem activationTraceNodes_intersection_iff_collider (node : Fin S.count)
    (onPath : .observed node ∈ normal.cutPath.nodes) :
    normal.activationTraceNodes pivot forest node = true ↔ normal.colliderSeeds node = true := by
  constructor
  · intro selected
    rcases (normal.activationTraceNodes_eq_true_iff pivot forest node).mp selected with ⟨collider, seed, visited⟩
    rcases (normal.colliderSeeds_eq_true_iff collider).mp seed with ⟨before, after, previous, next, window, actual⟩
    have same := normal.activation_forest_path_intersection_eq_collider pivot forest before after previous next collider
      window actual node visited onPath
    exact same ▸ seed
  · exact normal.colliderSeeds_subset_activationTraceNodes pivot forest node

/-! ## Small overlap is a partition, not a disjointness assumption -/

/-- Rows of the actual activation union outside an arbitrary mandatory
set.  In the conditional countermodel that set is the entire small forest. -/
def activationTraceOutside (mandatory : NodeSet S) : NodeSet S :=
  NodeSet.diff (normal.activationTraceNodes pivot forest) mandatory

/-- An outside activation row is genuinely outside the mandatory set;
there is no duplicated installation of an inside-small activation row. -/
theorem activationTraceOutside_not_mandatory (mandatory : NodeSet S) (node : Fin S.count)
    (selected : normal.activationTraceOutside pivot forest mandatory node = true) : mandatory node = false := by
  simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp selected).2

/-- Every outside activation row also survives the full original action;
this is the second support condition of a background-interaction selection. -/
theorem activationTraceOutside_action_free (mandatory : NodeSet S) (node : Fin S.count)
    (selected : normal.activationTraceOutside pivot forest mandatory node = true) : query.action node = false :=
  normal.activationTraceNodes_action_free pivot forest node (Bool.and_eq_true_iff.mp selected).1

/-- Mandatory rows and the remaining activation rows reconstruct their
ordinary union.  An overlapping row is present once, not canceled by XOR
and not omitted by a proposed disjointness hypothesis. -/
theorem mandatory_union_activationTraceOutside (mandatory : NodeSet S) :
    NodeSet.union mandatory (normal.activationTraceOutside pivot forest mandatory) =
      NodeSet.union mandatory (normal.activationTraceNodes pivot forest) := by
  funext node
  change (mandatory node || (normal.activationTraceNodes pivot forest node && !(mandatory node))) =
    (mandatory node || normal.activationTraceNodes pivot forest node)
  cases mandatory node <;> cases normal.activationTraceNodes pivot forest node <;> rfl

end ConditionalBackdoorPathNormalForm

end Causality
end Thesis
