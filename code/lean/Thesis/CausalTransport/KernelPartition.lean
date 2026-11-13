import Thesis.CausalTransport.KernelSeparation

namespace Thesis
namespace Causality

/-!
# Exact finite c-component partitions for product compilation

The product compiler needs more than coverage: grouping vertex factors by
c-component must neither omit a vertex nor repeat it.  This module proves
pairwise disjointness of the actual executable collector, then obtains a
permutation between its flattened component enumerations and the host's
reverse topological enumeration.  No interval or component-order hypothesis
is imposed.

A vertex's component is found by a Boolean finite-list search.  Coverage
proves that this search succeeds on a selected vertex; the selected component
is data returned by the search, never a witness chosen from an existential
proposition.  Uniqueness follows from the proved disjoint partition.
-/

namespace ObservedGraph

/-- A newly discovered component misses every earlier component whose
root-membership test was false.  Shared membership would give a reversed
bidirected walk back to the new root, contradicting that test. -/
private theorem cComponentOf_disjoint_of_root_outside
    (G : ObservedGraph S) (nodes : NodeSet S) (root otherRoot : Fin S.count)
    (rootSelected : nodes root = true) (otherSelected : nodes otherRoot = true)
    (outside : G.cComponentOf nodes otherRoot root = false) :
    NodeSet.Disjoint (G.cComponentOf nodes root) (G.cComponentOf nodes otherRoot) := by
  intro node selected
  cases otherInside : G.cComponentOf nodes otherRoot node with
  | false => rfl
  | true =>
      have first := (cComponentOf_eq_true_iff G nodes rootSelected).mp selected
      have second := (cComponentOf_eq_true_iff G nodes otherSelected).mp otherInside
      have returns := (cComponentOf_eq_true_iff G nodes otherSelected).mpr
        (second.trans first.symm)
      rw [outside] at returns
      cases returns

/-- The collector preserves a disjoint family of genuine rooted components.
Its reverse at termination changes only list order, not disjointness. -/
private theorem cComponentsCollect_pairwise_disjoint
    (G : ObservedGraph S) (nodes : NodeSet S) (pending : List (Fin S.count))
    (acc : List (NodeSet S))
    (rooted : forall component, component ∈ acc -> Exists fun root =>
      nodes root = true ∧ component = G.cComponentOf nodes root)
    (disjoint : acc.Pairwise NodeSet.Disjoint) :
    (G.cComponentsCollect nodes pending acc).Pairwise NodeSet.Disjoint := by
  induction pending generalizing acc with
  | nil =>
      apply List.pairwise_reverse.mpr
      exact disjoint.imp (fun separate => NodeSet.Disjoint.symm separate)
  | cons root rest inductionHypothesis =>
      cases selected : nodes root with
      | false =>
          simpa only [cComponentsCollect, selected, Bool.false_eq_true, ↓reduceIte] using
            inductionHypothesis acc rooted disjoint
      | true =>
          cases seen : acc.any (fun component => component root) with
          | true =>
              simpa only [cComponentsCollect, selected, seen, ↓reduceIte] using
                inductionHypothesis acc rooted disjoint
          | false =>
              have newDisjoint : forall component, component ∈ acc ->
                  NodeSet.Disjoint (G.cComponentOf nodes root) component := by
                intro component listed
                rcases rooted component listed with ⟨otherRoot, otherSelected, rfl⟩
                have outside : G.cComponentOf nodes otherRoot root = false := by
                  cases inside : G.cComponentOf nodes otherRoot root with
                  | false => rfl
                  | true =>
                      have contradiction : acc.any (fun component => component root) = true :=
                        List.any_eq_true.mpr
                        ⟨G.cComponentOf nodes otherRoot, listed, inside⟩
                      rw [seen] at contradiction
                      cases contradiction
                exact cComponentOf_disjoint_of_root_outside G nodes root otherRoot
                  selected otherSelected outside
              have newRooted : forall component,
                  component ∈ G.cComponentOf nodes root :: acc -> Exists fun seed =>
                    nodes seed = true ∧ component = G.cComponentOf nodes seed := by
                intro component listed
                rcases List.mem_cons.mp listed with first | later
                · exact ⟨root, selected, first⟩
                · exact rooted component later
              simpa only [cComponentsCollect, selected, seen, Bool.false_eq_true, ↓reduceIte] using
                inductionHypothesis (G.cComponentOf nodes root :: acc) newRooted
                  (List.Pairwise.cons newDisjoint disjoint)

/-- Actual listed c-components are pairwise disjoint, not merely individually
connected or known to cover the host. -/
theorem cComponents_pairwise_disjoint (G : ObservedGraph S) (nodes : NodeSet S) :
    (G.cComponents nodes).Pairwise NodeSet.Disjoint :=
  cComponentsCollect_pairwise_disjoint G nodes (NodeSet.enumerated S) []
    (fun _component absent => False.elim (List.not_mem_nil absent)) .nil

/-- Two pieces of a disjoint family sharing a vertex are the same piece.
List induction avoids deciding equality of functional Boolean node sets. -/
private theorem equal_of_pairwise_disjoint_shared
    (components : List (NodeSet S)) (disjoint : components.Pairwise NodeSet.Disjoint)
    {first second : NodeSet S} (firstListed : first ∈ components) (secondListed : second ∈ components)
    (node : Fin S.count) (firstInside : first node = true) (secondInside : second node = true) :
    first = second := by
  induction components with
  | nil => exact False.elim (List.not_mem_nil firstListed)
  | cons head tail inductionHypothesis =>
      have separate := List.pairwise_cons.mp disjoint
      rcases List.mem_cons.mp firstListed with firstHead | firstTail
      · subst first
        rcases List.mem_cons.mp secondListed with secondHead | secondTail
        · exact secondHead.symm
        · have impossible := separate.1 second secondTail node firstInside
          rw [secondInside] at impossible
          cases impossible
      · rcases List.mem_cons.mp secondListed with secondHead | secondTail
        · subst second
          have impossible := separate.1 first firstTail node secondInside
          rw [firstInside] at impossible
          cases impossible
        · exact inductionHypothesis separate.2 firstTail secondTail

/-- A failed Boolean `find?` excludes each listed matching element.
This small structural proof has no dependency on classical list characterizations. -/
private theorem find?_none_false (values : List X) (predicate : X -> Bool)
    (missing : values.find? predicate = none) {value : X} (member : value ∈ values) :
    predicate value = false := by
  induction values with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail inductionHypothesis =>
      cases selected : predicate head with
      | true => simp only [List.find?, selected] at missing; cases missing
      | false =>
          have tailMissing : tail.find? predicate = none := by
            simpa only [List.find?, selected, Bool.false_eq_true, ↓reduceIte] using missing
          rcases List.mem_cons.mp member with same | later
          · subst value; exact selected
          · exact inductionHypothesis tailMissing later

/-- The component returned by the explicit first-match search.  The empty
fallback is used only outside the host; selected vertices never use it. -/
def componentAt (G : ObservedGraph S) (nodes : NodeSet S) (node : Fin S.count) : NodeSet S :=
  ((G.cComponents nodes).find? (fun component => component node)).getD NodeSet.empty

/-- Coverage establishes success of the computed search and its membership
properties, without choosing a component from the coverage proposition. -/
theorem componentAt_spec (G : ObservedGraph S) (nodes : NodeSet S) (node : Fin S.count)
    (selected : nodes node = true) :
    G.componentAt nodes node ∈ G.cComponents nodes ∧ G.componentAt nodes node node = true := by
  cases found : (G.cComponents nodes).find? (fun component => component node) with
  | none =>
      rcases cComponents_covers G nodes selected with ⟨component, listed, inside⟩
      have impossible := find?_none_false (G.cComponents nodes) (fun component => component node)
        found listed
      change component node = false at impossible
      rw [inside] at impossible
      cases impossible
  | some component =>
      simpa only [componentAt, found, Option.getD_some] using find?_eq_some_mem _ _ found

/-- Any listed component containing the vertex is exactly the search result.
This aligns a global vertex-factor function with every component block. -/
theorem componentAt_eq_of_mem (G : ObservedGraph S) (nodes : NodeSet S)
    {component : NodeSet S} (listed : component ∈ G.cComponents nodes)
    (node : Fin S.count) (inside : component node = true) :
    G.componentAt nodes node = component := by
  have computed := G.componentAt_spec nodes node (cComponents_subset G nodes listed node inside)
  exact equal_of_pairwise_disjoint_shared (G.cComponents nodes) (G.cComponents_pairwise_disjoint nodes)
    computed.1 listed node computed.2 inside

end ObservedGraph

/-! ## Flattened enumerations retain every factor exactly once -/

/-- Reverse enumeration preserves nodup via a constructive list permutation. -/
private theorem reverse_members_nodup (nodes : NodeSet S) : (NodeSet.members nodes).reverse.Nodup :=
  (List.reverse_perm _).symm.nodup (NodeSet.nodup_members nodes)

/-- Flattening reverse member lists of disjoint pieces introduces no duplicates.
Both within-piece uniqueness and between-piece disjointness are needed. -/
private theorem disjoint_component_members_flatten_nodup
    (components : List (NodeSet S)) (disjoint : components.Pairwise NodeSet.Disjoint) :
    (components.map (fun component => (NodeSet.members component).reverse)).flatten.Nodup := by
  induction components with
  | nil => exact .nil
  | cons component rest inductionHypothesis =>
      have separate := List.pairwise_cons.mp disjoint
      rw [List.map_cons, List.flatten_cons]
      apply List.nodup_append.mpr
      refine ⟨reverse_members_nodup component, inductionHypothesis separate.2, ?_⟩
      intro first firstMember second secondMember same
      rcases List.mem_flatten.mp secondMember with ⟨vertices, verticesMember, secondIn⟩
      rcases List.mem_map.mp verticesMember with ⟨other, otherListed, rfl⟩
      have firstInside := (NodeSet.mem_members_iff component first).mp
        (List.mem_reverse.mp firstMember)
      have secondInside := (NodeSet.mem_members_iff other second).mp (List.mem_reverse.mp secondIn)
      have impossible := separate.1 other otherListed first firstInside
      rw [same, secondInside] at impossible
      cases impossible

/-- Constructive permutation of duplicate-free enumerations with the same
members.  This proof stays on finite list data and deliberately does not
import the soundness module's unrelated enumeration utilities. -/
private theorem permutation_of_nodup_mem_iff {X : Type} [DecidableEq X]
    (left right : List X) (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (members : forall value, value ∈ left ↔ value ∈ right) : left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons head tail =>
          exact False.elim (List.not_mem_nil ((members head).mpr (List.mem_cons.mpr (Or.inl rfl))))
  | cons head tail inductionHypothesis =>
      have leftParts := List.nodup_cons.mp leftNodup
      have headMember := (members head).mp (List.mem_cons.mpr (Or.inl rfl))
      rcases List.append_of_mem headMember with ⟨before, after, equality⟩
      subst right
      have rightParts := List.nodup_append.mp rightNodup
      have afterParts := List.nodup_cons.mp rightParts.2.1
      have removedNodup : (before ++ after).Nodup := List.nodup_append.mpr
        ⟨rightParts.1, afterParts.2, fun first firstMem second secondMem same =>
          rightParts.2.2 first firstMem second (List.mem_cons.mpr (Or.inr secondMem)) same⟩
      have headAbsent : head ∉ before ++ after := by
        intro occurs
        rcases List.mem_append.mp occurs with inBefore | inAfter
        · exact rightParts.2.2 head inBefore head (List.mem_cons.mpr (Or.inl rfl)) rfl
        · exact afterParts.1 inAfter
      have remainingMembers : forall value, value ∈ tail ↔ value ∈ before ++ after := by
        intro value
        constructor
        · intro later
          have different : value ≠ head := by intro equal; subst value; exact leftParts.1 later
          have occurrence := (members value).mp (List.mem_cons.mpr (Or.inr later))
          rcases List.mem_append.mp occurrence with inBefore | inHeadAfter
          · exact List.mem_append.mpr (Or.inl inBefore)
          · rcases List.mem_cons.mp inHeadAfter with same | inAfter
            · exact False.elim (different same)
            · exact List.mem_append.mpr (Or.inr inAfter)
        · intro remaining
          have occurrence : value ∈ before ++ head :: after := by
            rcases List.mem_append.mp remaining with inBefore | inAfter
            · exact List.mem_append.mpr (Or.inl inBefore)
            · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr inAfter)))
          rcases List.mem_cons.mp ((members value).mpr occurrence) with same | later
          · subst value; exact False.elim (headAbsent remaining)
          · exact later
      exact (List.Perm.cons head (inductionHypothesis (before ++ after) leftParts.2
        removedNodup remainingMembers)).trans List.perm_middle.symm

/-- The actual c-component grouping is an exact permutation of the host's
reverse topological vertices.  Components may interleave arbitrarily. -/
theorem ObservedGraph.cComponents_members_permutation (G : ObservedGraph S) (nodes : NodeSet S) :
    (NodeSet.members nodes).reverse.Perm
      ((G.cComponents nodes).map (fun component => (NodeSet.members component).reverse)).flatten := by
  apply permutation_of_nodup_mem_iff _ _ (reverse_members_nodup nodes)
    (disjoint_component_members_flatten_nodup _ (G.cComponents_pairwise_disjoint nodes))
  intro node
  constructor
  · intro member
    have selected := (NodeSet.mem_members_iff nodes node).mp (List.mem_reverse.mp member)
    rcases cComponents_covers G nodes selected with ⟨component, listed, inside⟩
    exact List.mem_flatten.mpr ⟨(NodeSet.members component).reverse,
      List.mem_map.mpr ⟨component, listed, rfl⟩,
      List.mem_reverse.mpr ((NodeSet.mem_members_iff component node).mpr inside)⟩
  · intro member
    rcases List.mem_flatten.mp member with ⟨vertices, listedVertices, vertexMember⟩
    rcases List.mem_map.mp listedVertices with ⟨component, listed, rfl⟩
    have inside := (NodeSet.mem_members_iff component node).mp (List.mem_reverse.mp vertexMember)
    exact List.mem_reverse.mpr ((NodeSet.mem_members_iff nodes node).mpr
      (cComponents_subset G nodes listed node inside))

end Causality
end Thesis
