import Thesis.CausalTransport.ActivePathNormalization
import Thesis.CausalTransport.ActivePathTransport

namespace Thesis
namespace Causality

universe u

variable {S : ObservedSignature.{u}}

/-!
# Collider accounting at a directed activation detour

The collider-normal path is selected constructively in
`ActivePathNormalization`.  To use its optimality, a detour must be compared
with the original path at its actual changed windows.  Counting only the
removed source collider would be incorrect: the return vertex may become a
new collider, although every internal directed-detour vertex is a noncollider.

The accounting here splits a path at two displayed vertices.  All unchanged
prefix and suffix windows are retained, the source collider disappears, and
the return window contributes at most one collider.  If the count does not
decrease, exactly one earlier collider was replaced by the later return
vertex, and its greater observed rank improves the secondary objective.

The second half constructs the actual detour in the same mutilated expanded
graph.  It derives full-path simplicity and activity from the directed bridge,
its open internal vertices, its activated return, and the original path's
certificates.  It then proves score improvement and exclusion by optimality,
with reversal supplying the other traversal orientation.

Conditional application must still derive these local bridge certificates
at the first activation/path intersection.  Neither the numerical comparison
nor the generic surgery theorem silently supplies that extraction, solves
small-forest intersections, or constructs a conditional countermodel.
-/

namespace PathSpecification

/-! ## The single internal window created at a list join -/

/-- Joining `left ++ [middle]` to `middle :: right` creates just this one
additional internal window.  At either endpoint there is no such window. -/
def colliderJoinBool (G : ObservedGraph S) (m : GraphMutilation S)
    (left : List (SeparationNode S)) (middle : SeparationNode S) (right : List (SeparationNode S)) : Bool :=
  match left.getLast?, right.head? with
  | some previous, some next => isColliderBool G m previous middle next
  | _, _ => false

/-- A private weighted traversal proves count and rank identities together.
Its weights are executable naturals, not decisions about semantic properties. -/
private def colliderWeightSum (G : ObservedGraph S) (m : GraphMutilation S)
    (weight : SeparationNode S -> Nat) : List (SeparationNode S) -> Nat
  | [] => 0
  | [_] => 0
  | [_, _] => 0
  | previous :: middle :: next :: rest =>
      (if isColliderBool G m previous middle next then weight middle else 0) +
        colliderWeightSum G m weight (middle :: next :: rest)

private theorem colliderWeightSum_glue (G : ObservedGraph S) (m : GraphMutilation S)
    (weight : SeparationNode S -> Nat) (left : List (SeparationNode S))
    (middle : SeparationNode S) (right : List (SeparationNode S)) :
    colliderWeightSum G m weight (left ++ middle :: right) =
      colliderWeightSum G m weight (left ++ [middle]) +
      (if colliderJoinBool G m left middle right then weight middle else 0) +
      colliderWeightSum G m weight (middle :: right) := by
  induction left with
  | nil => simp only [List.nil_append, colliderWeightSum, colliderJoinBool, List.getLast?_nil,
      Bool.false_eq_true, if_false, Nat.zero_add]
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          cases right with
          | nil => rfl
          | cons next rest =>
              simp only [List.cons_append, List.nil_append, colliderWeightSum, colliderJoinBool,
                List.getLast?_singleton, List.head?_cons, Nat.zero_add]
              rfl
      | cons previous rest =>
          cases rest with
          | nil =>
              change (if isColliderBool G m first previous middle then weight previous else 0) +
                colliderWeightSum G m weight (previous :: middle :: right) = _
              simp only [List.cons_append, List.nil_append] at inductionHypothesis
              rw [inductionHypothesis]
              simp only [List.cons_append, List.nil_append, colliderWeightSum, colliderJoinBool,
                List.getLast?_cons_cons, List.getLast?_singleton, Nat.add_zero, Nat.zero_add, Nat.add_assoc]
              rfl
          | cons next rest =>
              simp only [List.cons_append, colliderWeightSum, colliderJoinBool, List.getLast?_cons_cons]
              simp only [List.cons_append] at inductionHypothesis
              rw [inductionHypothesis]
              simp only [Nat.add_assoc, colliderJoinBool, List.getLast?_cons_cons]

private theorem colliderWeightSum_one (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) : colliderWeightSum G m (fun _ => 1) nodes = colliderCount G m nodes := by
  induction nodes with
  | nil => rfl
  | cons previous tail inductionHypothesis =>
      cases tail with
      | nil => rfl
      | cons middle rest =>
          cases rest with
          | nil => rfl
          | cons next rest =>
              simpa only [colliderWeightSum, colliderCount] using
              congrArg (fun count => (if isColliderBool G m previous middle next then 1 else 0) + count)
                inductionHypothesis

private theorem colliderWeightSum_rank (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) :
    colliderWeightSum G m observedColliderRank nodes = colliderRankSum G m nodes := by
  induction nodes with
  | nil => rfl
  | cons previous tail inductionHypothesis =>
      cases tail with
      | nil => rfl
      | cons middle rest =>
          cases rest with
          | nil => rfl
          | cons next rest =>
              simpa only [colliderWeightSum, colliderRankSum] using
              congrArg (fun count => (if isColliderBool G m previous middle next then observedColliderRank middle else 0) + count)
                inductionHypothesis

/-- Reversal keeps each internal collider and its weight; only its two
parents exchange places.  The proof uses the single-join identity rather
than enumerating all triples or choosing their positions propositionally. -/
private theorem colliderWeightSum_reverse (G : ObservedGraph S) (m : GraphMutilation S)
    (weight : SeparationNode S -> Nat) (nodes : List (SeparationNode S)) :
    colliderWeightSum G m weight nodes.reverse = colliderWeightSum G m weight nodes := by
  induction nodes with
  | nil => rfl
  | cons previous tail inductionHypothesis =>
      cases tail with
      | nil => rfl
      | cons middle rest =>
          cases rest with
          | nil => rfl
          | cons next rest =>
              have reversed : (previous :: middle :: next :: rest).reverse =
                  (next :: rest).reverse ++ middle :: [previous] := by
                simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
                rfl
              rw [reversed, colliderWeightSum_glue]
              have prefixReverse : (next :: rest).reverse ++ [middle] = (middle :: next :: rest).reverse :=
                List.reverse_cons.symm
              rw [prefixReverse, inductionHypothesis]
              simp only [colliderJoinBool, List.getLast?_reverse, List.head?_cons, colliderWeightSum,
                isColliderBool, Bool.and_comm, Nat.zero_add, Nat.add_comm]
              rfl

/-- Reversing an actual path preserves its number of internal colliders. -/
theorem colliderCount_reverse (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) : colliderCount G m nodes.reverse = colliderCount G m nodes := by
  simpa only [colliderWeightSum_one] using colliderWeightSum_reverse G m (fun _ => 1) nodes

/-- The same observed collider ranks are counted after path reversal. -/
theorem colliderRankSum_reverse (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) : colliderRankSum G m nodes.reverse = colliderRankSum G m nodes := by
  simpa only [colliderWeightSum_rank] using colliderWeightSum_reverse G m observedColliderRank nodes

/-- Both normalization objectives, hence the whole score, are orientation
independent.  A backward intersection can therefore use the forward proof. -/
theorem colliderNormalizationScore_reverse (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) :
    colliderNormalizationScore G m nodes.reverse = colliderNormalizationScore G m nodes := by
  simp only [colliderNormalizationScore, colliderCount_reverse, colliderRankSum_reverse]

/-- All old internal prefix/suffix windows remain; only the displayed join
can add a collider.  Endpoint joins contribute zero by definition. -/
theorem colliderCount_glue (G : ObservedGraph S) (m : GraphMutilation S)
    (left : List (SeparationNode S)) (middle : SeparationNode S) (right : List (SeparationNode S)) :
    colliderCount G m (left ++ middle :: right) = colliderCount G m (left ++ [middle]) +
      (if colliderJoinBool G m left middle right then 1 else 0) + colliderCount G m (middle :: right) := by
  simpa only [colliderWeightSum_one] using colliderWeightSum_glue G m (fun _ => 1) left middle right

/-- The same join identity tracks the rank of precisely that new collider.
It cannot count the rank of an endpoint or an open noncollider. -/
theorem colliderRankSum_glue (G : ObservedGraph S) (m : GraphMutilation S)
    (left : List (SeparationNode S)) (middle : SeparationNode S) (right : List (SeparationNode S)) :
    colliderRankSum G m (left ++ middle :: right) = colliderRankSum G m (left ++ [middle]) +
      (if colliderJoinBool G m left middle right then observedColliderRank middle else 0) +
      colliderRankSum G m (middle :: right) := by
  simpa only [colliderWeightSum_rank] using colliderWeightSum_glue G m observedColliderRank left middle right

/-- A zero collider count also forces zero collider-rank sum.  This local
fact is needed for the removed middle segment when a detour preserves count. -/
theorem colliderRankSum_eq_zero_of_count_zero (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (zero : colliderCount G m nodes = 0) : colliderRankSum G m nodes = 0 := by
  induction nodes with
  | nil => rfl
  | cons previous tail inductionHypothesis =>
      cases tail with
      | nil => rfl
      | cons middle rest =>
          cases rest with
          | nil => rfl
          | cons next rest =>
              cases collider : isColliderBool G m previous middle next with
              | true => simp only [colliderCount, collider, if_true] at zero; omega
              | false =>
                  simp only [colliderCount, collider, Bool.false_eq_true, if_false, Nat.zero_add] at zero
                  simpa only [colliderRankSum, collider, Bool.false_eq_true, if_false, Nat.zero_add] using
                    inductionHypothesis zero

/-! ## Directed detours have no internal colliders -/

/-- A directed edge leaving the middle vertex rules out the reverse edge
required by a collider, by the strict expanded-DAG rank. -/
private theorem isColliderBool_false_of_outgoing (G : ObservedGraph S) (m : GraphMutilation S)
    (previous middle next : SeparationNode S) (outgoing : G.expandedMutilatedEdge m middle next = true) :
    isColliderBool G m previous middle next = false := by
  cases collider : isColliderBool G m previous middle next with
  | false => rfl
  | true => exact False.elim (G.not_collider_of_outgoing m outgoing
      ((IsCollider_iff_isColliderBool G m previous middle next).mpr collider))

/-- Every internal vertex of an actual directed list is a noncollider.
No statement about activation or conditioning is needed for this count. -/
theorem colliderCount_eq_zero_of_directed (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S))
    (directed : Consecutive (fun left right => G.expandedMutilatedEdge m left right = true) nodes) :
    colliderCount G m nodes = 0 := by
  induction nodes with
  | nil => rfl
  | cons previous tail inductionHypothesis =>
      cases tail with
      | nil => rfl
      | cons middle rest =>
          cases rest with
          | nil => rfl
          | cons next rest =>
              have notCollider := isColliderBool_false_of_outgoing G m previous middle next directed.2.1
              simp only [colliderCount, notCollider, Bool.false_eq_true, if_false, Nat.zero_add]
              exact inductionHypothesis directed.2

/-- Rank sums vanish on the same directed list, with no extra path flag. -/
theorem colliderRankSum_eq_zero_of_directed (G : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S))
    (directed : Consecutive (fun left right => G.expandedMutilatedEdge m left right = true) nodes) :
    colliderRankSum G m nodes = 0 :=
  colliderRankSum_eq_zero_of_count_zero G m nodes (colliderCount_eq_zero_of_directed G m nodes directed)

/-! ## A disappearing source collider and a possibly new return collider -/

/-- Exact comparison for a forward detour between two displayed vertices.
The unchanged prefix and suffix are identical lists in both candidates.
The detour has no internal colliders, removes the source collider, and its
return vertex has greater observed rank.  Even if that return becomes a new
collider, the resulting list strictly improves the lexicographic objective.

The source-join Boolean premises name the actual changed windows.  A later
active-path constructor must derive them from the old collider and outgoing
detour edge; this lemma does not reinterpret them as failure-readiness flags. -/
theorem colliderObjectives_improve_of_directed_detour (G : ObservedGraph S) (m : GraphMutilation S)
    (left between via right : List (SeparationNode S)) (source returned : SeparationNode S)
    (oldCollider : colliderJoinBool G m left source (between ++ returned :: right) = true)
    (newNonCollider : colliderJoinBool G m left source (via ++ returned :: right) = false)
    (directed : Consecutive (fun parent child => G.expandedMutilatedEdge m parent child = true)
      (source :: via ++ [returned]))
    (later : observedColliderRank source < observedColliderRank returned) :
    colliderCount G m (left ++ source :: (via ++ returned :: right)) <
      colliderCount G m (left ++ source :: (between ++ returned :: right)) ∨
    (colliderCount G m (left ++ source :: (via ++ returned :: right)) =
      colliderCount G m (left ++ source :: (between ++ returned :: right)) ∧
      colliderRankSum G m (left ++ source :: (between ++ returned :: right)) <
        colliderRankSum G m (left ++ source :: (via ++ returned :: right))) := by
  have bridgeCount := colliderCount_eq_zero_of_directed G m (source :: via ++ [returned]) directed
  have bridgeRank := colliderRankSum_eq_zero_of_directed G m (source :: via ++ [returned]) directed
  have oldCount := colliderCount_glue G m left source (between ++ returned :: right)
  have newCount := colliderCount_glue G m left source (via ++ returned :: right)
  have oldMiddleCount := colliderCount_glue G m (source :: between) returned right
  have newMiddleCount := colliderCount_glue G m (source :: via) returned right
  have oldRank := colliderRankSum_glue G m left source (between ++ returned :: right)
  have newRank := colliderRankSum_glue G m left source (via ++ returned :: right)
  have oldMiddleRank := colliderRankSum_glue G m (source :: between) returned right
  have newMiddleRank := colliderRankSum_glue G m (source :: via) returned right
  simp only [List.cons_append] at bridgeCount bridgeRank oldMiddleCount newMiddleCount oldMiddleRank newMiddleRank
  rw [oldCollider] at oldCount oldRank
  rw [newNonCollider] at newCount newRank
  rw [bridgeCount] at newMiddleCount
  rw [bridgeRank] at newMiddleRank
  simp only [if_true, Bool.false_eq_true, if_false, Nat.add_zero, Nat.zero_add] at oldCount newCount oldRank newRank newMiddleCount newMiddleRank
  simp only [List.cons_append] at *
  cases oldReturn : colliderJoinBool G m (source :: between) returned right <;>
    cases newReturn : colliderJoinBool G m (source :: via) returned right <;>
    simp only [oldReturn, newReturn, Bool.false_eq_true, if_false, if_true] at oldMiddleCount newMiddleCount oldMiddleRank newMiddleRank
  · exact Or.inl (by omega)
  · by_cases fewer : colliderCount G m (left ++ source :: (via ++ returned :: right)) <
        colliderCount G m (left ++ source :: (between ++ returned :: right))
    · exact Or.inl fewer
    · have equalCounts : colliderCount G m (left ++ source :: (via ++ returned :: right)) =
          colliderCount G m (left ++ source :: (between ++ returned :: right)) := by omega
      have middleZero : colliderCount G m (source :: (between ++ [returned])) = 0 := by omega
      have middleRankZero := colliderRankSum_eq_zero_of_count_zero G m _ middleZero
      exact Or.inr ⟨equalCounts, by omega⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)

/-! ## Activity of the actual detour, including its return window -/

/-- Replacing the old previous neighbour by a new incoming edge preserves
the return window's activity when the returned vertex is activated.  If it
was conditioned, old activity made it a collider, so the retained next edge
still points into it.  Thus a conditioned return cannot become a noncollider. -/
theorem TripleActive.ofIncomingDetour {G : ObservedGraph S} {m : GraphMutilation S}
    {conditioned : NodeSet S} {oldPrevious previous middle next : SeparationNode S}
    (old : TripleActive G m conditioned oldPrevious middle next)
    (incoming : G.expandedMutilatedEdge m previous middle = true)
    (activated : ColliderActivated G m conditioned middle) : TripleActive G m conditioned previous middle next := by
  cases collider : isColliderBool G m previous middle next with
  | true => exact Or.inl ⟨(IsCollider_iff_isColliderBool G m previous middle next).mpr collider, activated⟩
  | false =>
      have notCollider : Not (IsCollider G m previous middle next) := by
        intro found
        have positive := (IsCollider_iff_isColliderBool G m previous middle next).mp found
        rw [collider] at positive
        cases positive
      rcases old with wasCollider | wasOpen
      · exact False.elim (notCollider ⟨incoming, wasCollider.1.2⟩)
      · exact Or.inr ⟨notCollider, wasOpen.2⟩

/-- The internal vertices of a directed bridge are active exactly because
they are open noncolliders.  Its endpoints need not be open for this internal
certificate; in particular the return vertex is allowed to be conditioned. -/
theorem InternalTriplesActive.ofDirectedBridge (G : ObservedGraph S) (m : GraphMutilation S)
    (conditioned : NodeSet S) (source returned : SeparationNode S) (via : List (SeparationNode S))
    (directed : Consecutive (fun parent child => G.expandedMutilatedEdge m parent child = true)
      (source :: (via ++ [returned])))
    (openVia : forall node, node ∈ via -> ObservedGraph.blockedBy conditioned node = false) :
    InternalTriplesActive G m conditioned (source :: (via ++ [returned])) := by
  induction via generalizing source with
  | nil => exact .pair source returned
  | cons middle tail inductionHypothesis =>
      have middleOpen := openVia middle (List.mem_cons.mpr (Or.inl rfl))
      have restOpen : forall node, node ∈ tail -> ObservedGraph.blockedBy conditioned node = false :=
        fun node member => openVia node (List.mem_cons.mpr (Or.inr member))
      cases tail with
      | nil => exact .step (Or.inr ⟨G.not_collider_of_outgoing m directed.2.1, middleOpen⟩) (.pair middle returned)
      | cons next rest =>
          exact .step (Or.inr ⟨G.not_collider_of_outgoing m directed.2.1, middleOpen⟩)
            (inductionHypothesis middle directed.2 restOpen)

/-- The outgoing first detour edge derives the disappearing source window.
It holds for any old prefix, including an empty one; no noncollider flag is
requested independently of the actual directed bridge. -/
theorem colliderJoinBool_false_of_directed_bridge (G : ObservedGraph S) (m : GraphMutilation S)
    (left via right : List (SeparationNode S)) (source returned : SeparationNode S)
    (directed : Consecutive (fun parent child => G.expandedMutilatedEdge m parent child = true)
      (source :: (via ++ [returned]))) :
    colliderJoinBool G m left source (via ++ returned :: right) = false := by
  cases via with
  | nil =>
      cases last : left.getLast? with
      | none => simp only [colliderJoinBool, last]
      | some previous =>
          simpa only [colliderJoinBool, last, List.nil_append, List.head?_cons] using
            isColliderBool_false_of_outgoing G m previous source returned directed.1
  | cons next rest =>
      cases last : left.getLast? with
      | none => simp only [colliderJoinBool, last]
      | some previous =>
          simpa only [colliderJoinBool, last, List.cons_append, List.head?_cons] using
            isColliderBool_false_of_outgoing G m previous source next directed.1

private theorem consecutive_suffix {α : Type _} {relation : α -> α -> Prop}
    (before : List α) (node : α) (after : List α)
    (consecutive : Consecutive relation (before ++ node :: after)) : Consecutive relation (node :: after) := by
  have suffix := Consecutive.drop before.length (before ++ node :: after) consecutive
  simpa only [List.drop_append_length] using suffix

/-- Removing the old middle segment and inserting a directed bridge yields
an actual active path.  The bridge's internal vertices avoid the original
path, so simplicity is proved rather than supplied for the completed detour.
All return-window cases, including a conditioned return and an outcome endpoint,
use the original activity certificates.

The premises are local certificates of displayed graph/list data.  Conditional
application must obtain them from the first activation/path intersection;
this constructor alone does not assume or prove that such intersections vanish. -/
def ActivePath.ofDirectedColliderDetour {G : ObservedGraph S} {m : GraphMutilation S}
    {conditioned : NodeSet S} {start finish : SeparationNode S}
    (path : ActivePath G m conditioned start finish)
    (left between via right : List (SeparationNode S)) (source returned : SeparationNode S)
    (split : path.nodes = left ++ source :: (between ++ returned :: right))
    (oldCollider : colliderJoinBool G m left source (between ++ returned :: right) = true)
    (directed : Consecutive (fun parent child => G.expandedMutilatedEdge m parent child = true)
      (source :: (via ++ [returned])))
    (bridgeSimple : (source :: (via ++ [returned])).Nodup)
    (sourceOpen : ObservedGraph.blockedBy conditioned source = false)
    (openVia : forall node, node ∈ via -> ObservedGraph.blockedBy conditioned node = false)
    (activated : ColliderActivated G m conditioned returned)
    (avoids : forall node, node ∈ via -> node ∈ path.nodes -> False) :
    ActivePath G m conditioned start finish := by
  let front := left ++ [source]
  let suffix := returned :: right
  have oldNodes : path.nodes = front ++ between ++ suffix := by
    simpa only [front, suffix, List.append_assoc, List.singleton_append] using split
  have prefixSimple : front.Nodup :=
    ObservedGraph.nodup_prefix_append (split ▸ path.simple)
  have suffixSimple : suffix.Nodup := by
    have parts := List.nodup_append.mp (oldNodes ▸ path.simple)
    exact parts.2.1
  have viaSimple : via.Nodup :=
    (List.nodup_append.mp (List.nodup_cons.mp bridgeSimple).2).1
  have prefixMember : forall node, node ∈ front -> node ∈ path.nodes := by
    intro node member
    rw [oldNodes]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl member)))
  have suffixMember : forall node, node ∈ suffix -> node ∈ path.nodes := by
    intro node member
    rw [oldNodes]
    exact List.mem_append.mpr (Or.inr member)
  have prefixSuffixDisjoint : forall node, node ∈ front -> node ∈ suffix -> False := by
    intro node inPrefix inSuffix
    exact (List.nodup_append.mp (oldNodes ▸ path.simple)).2.2 node
      (List.mem_append.mpr (Or.inl inPrefix)) node inSuffix rfl
  have viaSuffixSimple : (via ++ suffix).Nodup :=
    nodup_append_of_disjoint viaSimple suffixSimple
      (fun node inVia inSuffix => avoids node inVia (suffixMember node inSuffix))
  have newSimple : (front ++ via ++ suffix).Nodup := by
    rw [List.append_assoc]
    apply nodup_append_of_disjoint prefixSimple viaSuffixSimple
    intro node inPrefix member
    rcases List.mem_append.mp member with inVia | inSuffix
    · exact avoids node inVia (prefixMember node inPrefix)
    · exact prefixSuffixDisjoint node inPrefix inSuffix
  have prefixAdjacent := Consecutive.prefix_append left source (between ++ returned :: right)
    (split ▸ path.adjacent)
  have suffixAdjacent := consecutive_suffix (front ++ between) returned right (oldNodes ▸ path.adjacent)
  have bridgeAdjacent : Consecutive (Adjacent G m) (source :: (via ++ [returned])) :=
    Consecutive.mono (fun _ _ edge => Or.inl edge) _ directed
  have routeAdjacent : Consecutive (Adjacent G m) ((source :: via) ++ suffix) :=
    Consecutive.overlap_glue bridgeAdjacent suffixAdjacent
      (show (source :: (via ++ [returned])) = (source :: via) ++ returned :: [] by simp only [List.cons_append])
      (show suffix = [] ++ returned :: right from rfl)
  have newAdjacent : Consecutive (Adjacent G m) (front ++ via ++ suffix) := by
    have glued := Consecutive.overlap_glue prefixAdjacent routeAdjacent
      (show front = left ++ source :: [] from rfl)
      (show (source :: via) ++ suffix = [] ++ source :: (via ++ suffix) from rfl)
    simpa only [front, suffix, List.append_assoc, List.singleton_append] using glued
  have prefixActive : InternalTriplesActive G m conditioned front := by
    have active := path.internal_active.take front.length
    rw [oldNodes, List.append_assoc, List.take_left] at active
    exact active
  have suffixActive := InternalTriplesActive.suffix_append (front ++ between) returned right
    (oldNodes ▸ path.internal_active)
  have bridgeActive := InternalTriplesActive.ofDirectedBridge G m conditioned source returned via directed openVia
  have routeActive : InternalTriplesActive G m conditioned ((source :: via) ++ suffix) := by
    apply InternalTriplesActive.glue_at (source :: via) returned right
      (by simpa only [List.cons_append] using bridgeActive) suffixActive
    intro previous next previousLast nextHead
    rcases List.getLast?_eq_some_iff.mp previousLast with ⟨beforeBridge, bridgeSplit⟩
    rcases List.head?_eq_some_iff.mp nextHead with ⟨after, rightSplit⟩
    have incoming : G.expandedMutilatedEdge m previous returned = true := by
      have shape : source :: (via ++ [returned]) = beforeBridge ++ previous :: [returned] := by
        simpa only [List.append_assoc, List.singleton_append, List.cons_append] using
          congrArg (fun nodes => nodes ++ [returned]) bridgeSplit
      exact Consecutive.pair_of_append beforeBridge [] previous returned (shape ▸ directed)
    let oldPrevious := (source :: between).getLast (List.cons_ne_nil source between)
    have oldLast : (source :: between).getLast? = some oldPrevious :=
      List.getLast?_eq_some_getLast (List.cons_ne_nil source between)
    rcases List.getLast?_eq_some_iff.mp oldLast with ⟨beforeOld, oldSplit⟩
    have oldActive : TripleActive G m conditioned oldPrevious returned next := by
      have shape : path.nodes = (left ++ beforeOld) ++ oldPrevious :: returned :: next :: after := by
        rw [split, rightSplit]
        have same := congrArg (fun nodes => left ++ nodes ++ returned :: next :: after) oldSplit
        simpa only [List.append_assoc, List.cons_append, List.singleton_append] using same
      exact InternalTriplesActive.triple_of_append (left ++ beforeOld) after oldPrevious returned next
        (shape ▸ path.internal_active)
    exact oldActive.ofIncomingDetour incoming activated
  have newActive : InternalTriplesActive G m conditioned (front ++ via ++ suffix) := by
    have route : InternalTriplesActive G m conditioned (source :: (via ++ suffix)) := by
      simpa only [List.cons_append] using routeActive
    have glued := InternalTriplesActive.glue_at left source (via ++ suffix) prefixActive route (by
      intro previous next _previousLast nextHead
      have outgoing : G.expandedMutilatedEdge m source next = true := by
        cases via with
        | nil =>
            have same : returned = next := Option.some.inj nextHead
            exact same ▸ directed.1
        | cons child rest =>
            have same : child = next := Option.some.inj nextHead
            exact same ▸ directed.1
      exact Or.inr ⟨G.not_collider_of_outgoing m outgoing, sourceOpen⟩)
    simpa only [front, List.append_assoc, List.singleton_append] using glued
  refine {
    nodes := front ++ via ++ suffix
    starts := ?_
    finishes := ?_
    simple := newSimple
    adjacent := newAdjacent
    internal_active := newActive
    source_open := path.source_open
    target_open := path.target_open
  }
  · have starts := split ▸ path.starts
    cases left with
    | nil => simp only [colliderJoinBool, List.getLast?_nil] at oldCollider; cases oldCollider
    | cons head rest => simpa only [front, List.cons_append, List.head?_cons] using starts
  · have finishes := ObservedGraph.getLast?_suffix_append (oldNodes ▸ path.finishes)
    simp only [List.getLast?_append, suffix, finishes, Option.some_or]

/-- The detour's complete list is explicit.  Later objective comparisons
can rewrite by this equality without inspecting proof-bearing path fields. -/
theorem ActivePath.ofDirectedColliderDetour_nodes {G : ObservedGraph S} {m : GraphMutilation S}
    {conditioned : NodeSet S} {start finish : SeparationNode S}
    (path : ActivePath G m conditioned start finish)
    (left between via right : List (SeparationNode S)) (source returned : SeparationNode S)
    (split : path.nodes = left ++ source :: (between ++ returned :: right))
    (oldCollider : colliderJoinBool G m left source (between ++ returned :: right) = true)
    (directed : Consecutive (fun parent child => G.expandedMutilatedEdge m parent child = true)
      (source :: (via ++ [returned])))
    (bridgeSimple : (source :: (via ++ [returned])).Nodup)
    (sourceOpen : ObservedGraph.blockedBy conditioned source = false)
    (openVia : forall node, node ∈ via -> ObservedGraph.blockedBy conditioned node = false)
    (activated : ColliderActivated G m conditioned returned)
    (avoids : forall node, node ∈ via -> node ∈ path.nodes -> False) :
    (path.ofDirectedColliderDetour left between via right source returned split oldCollider directed bridgeSimple
      sourceOpen openVia activated avoids).nodes = left ++ source :: (via ++ returned :: right) := by
  simp only [ActivePath.ofDirectedColliderDetour, List.append_assoc, List.cons_append, List.nil_append]

/-- The actual active detour strictly improves the collider-normal score.
The source noncollider fact is derived from its outgoing bridge edge, while
simplicity is derived by the constructor.  Both possible return-window
counts are included in the objective comparison. -/
theorem ActivePath.directedColliderDetour_score_lt {G : ObservedGraph S} {m : GraphMutilation S}
    {conditioned : NodeSet S} {start finish : SeparationNode S}
    (path : ActivePath G m conditioned start finish)
    (left between via right : List (SeparationNode S)) (source returned : SeparationNode S)
    (split : path.nodes = left ++ source :: (between ++ returned :: right))
    (oldCollider : colliderJoinBool G m left source (between ++ returned :: right) = true)
    (directed : Consecutive (fun parent child => G.expandedMutilatedEdge m parent child = true)
      (source :: (via ++ [returned])))
    (bridgeSimple : (source :: (via ++ [returned])).Nodup)
    (sourceOpen : ObservedGraph.blockedBy conditioned source = false)
    (openVia : forall node, node ∈ via -> ObservedGraph.blockedBy conditioned node = false)
    (activated : ColliderActivated G m conditioned returned)
    (avoids : forall node, node ∈ via -> node ∈ path.nodes -> False)
    (later : observedColliderRank source < observedColliderRank returned) :
    colliderNormalizationScore G m (path.ofDirectedColliderDetour left between via right source returned split
      oldCollider directed bridgeSimple sourceOpen openVia activated avoids).nodes <
      colliderNormalizationScore G m path.nodes := by
  let detour := path.ofDirectedColliderDetour left between via right source returned split
    oldCollider directed bridgeSimple sourceOpen openVia activated avoids
  have detourNodes := path.ofDirectedColliderDetour_nodes left between via right source returned split
    oldCollider directed bridgeSimple sourceOpen openVia activated avoids
  have improved := colliderObjectives_improve_of_directed_detour G m left between via right source returned
    oldCollider (colliderJoinBool_false_of_directed_bridge G m left via right source returned directed) directed later
  rw [← detourNodes, ← split] at improved
  rcases improved with fewer | sameCountAndLater
  · exact colliderNormalizationScore_lt_of_count_lt G m _ _ fewer
  · exact colliderNormalizationScore_lt_of_rank_lt G m _ _ detour.simple path.simple
      sameCountAndLater.1 sameCountAndLater.2

/-- A proved least-score active path admits no such forward detour.
The only global premise is actual score optimality, already furnished by
the finite witness constructor; there is no activation-avoidance assumption. -/
theorem ActivePath.noForwardColliderDetour {G : ObservedGraph S} {m : GraphMutilation S}
    {conditioned : NodeSet S} {start finish : SeparationNode S}
    (path : ActivePath G m conditioned start finish)
    (optimal : forall competitor : ActivePath G m conditioned start finish,
      colliderNormalizationScore G m path.nodes ≤ colliderNormalizationScore G m competitor.nodes)
    (left between via right : List (SeparationNode S)) (source returned : SeparationNode S)
    (split : path.nodes = left ++ source :: (between ++ returned :: right))
    (oldCollider : colliderJoinBool G m left source (between ++ returned :: right) = true)
    (directed : Consecutive (fun parent child => G.expandedMutilatedEdge m parent child = true)
      (source :: (via ++ [returned])))
    (bridgeSimple : (source :: (via ++ [returned])).Nodup)
    (sourceOpen : ObservedGraph.blockedBy conditioned source = false)
    (openVia : forall node, node ∈ via -> ObservedGraph.blockedBy conditioned node = false)
    (activated : ColliderActivated G m conditioned returned)
    (avoids : forall node, node ∈ via -> node ∈ path.nodes -> False)
    (later : observedColliderRank source < observedColliderRank returned) : False :=
  Nat.not_lt_of_ge
    (optimal (path.ofDirectedColliderDetour left between via right source returned split
      oldCollider directed bridgeSimple sourceOpen openVia activated avoids))
    (path.directedColliderDetour_score_lt left between via right source returned split
      oldCollider directed bridgeSimple sourceOpen openVia activated avoids later)

/-- Optimality transports to the reversed active path.  Its competitors
are reversed back into competitors of the original path, with exactly the
same collider score.  This is a theorem, not a second optimization search. -/
theorem ActivePath.reverse_colliderScore_optimal {G : ObservedGraph S} {m : GraphMutilation S}
    {conditioned : NodeSet S} {start finish : SeparationNode S}
    (path : ActivePath G m conditioned start finish)
    (optimal : forall competitor : ActivePath G m conditioned start finish,
      colliderNormalizationScore G m path.nodes ≤ colliderNormalizationScore G m competitor.nodes) :
    forall competitor : ActivePath G m conditioned finish start,
      colliderNormalizationScore G m path.reverse.nodes ≤ colliderNormalizationScore G m competitor.nodes := by
  intro competitor
  have bound := optimal competitor.reverse
  change colliderNormalizationScore G m path.nodes ≤ colliderNormalizationScore G m competitor.nodes.reverse at bound
  change colliderNormalizationScore G m path.nodes.reverse ≤ colliderNormalizationScore G m competitor.nodes
  simpa only [colliderNormalizationScore_reverse] using bound

/-- Returning before the original collider is excluded by reversing the
whole active path and using its transported optimality.  The local directed
bridge is not reversed: it still runs from the collider to its later-ranked
return vertex, exactly as the activation route does in the original DAG. -/
theorem ActivePath.noBackwardColliderDetour {G : ObservedGraph S} {m : GraphMutilation S}
    {conditioned : NodeSet S} {start finish : SeparationNode S}
    (path : ActivePath G m conditioned start finish)
    (optimal : forall competitor : ActivePath G m conditioned start finish,
      colliderNormalizationScore G m path.nodes ≤ colliderNormalizationScore G m competitor.nodes)
    (left between via right : List (SeparationNode S)) (source returned : SeparationNode S)
    (split : path.reverse.nodes = left ++ source :: (between ++ returned :: right))
    (oldCollider : colliderJoinBool G m left source (between ++ returned :: right) = true)
    (directed : Consecutive (fun parent child => G.expandedMutilatedEdge m parent child = true)
      (source :: (via ++ [returned])))
    (bridgeSimple : (source :: (via ++ [returned])).Nodup)
    (sourceOpen : ObservedGraph.blockedBy conditioned source = false)
    (openVia : forall node, node ∈ via -> ObservedGraph.blockedBy conditioned node = false)
    (activated : ColliderActivated G m conditioned returned)
    (avoids : forall node, node ∈ via -> node ∈ path.reverse.nodes -> False)
    (later : observedColliderRank source < observedColliderRank returned) : False :=
  path.reverse.noForwardColliderDetour (path.reverse_colliderScore_optimal optimal)
    left between via right source returned split oldCollider directed bridgeSimple sourceOpen openVia activated avoids later

end PathSpecification

end Causality
end Thesis
