import Thesis.CausalTransport.ActivePathTransport
import Thesis.Causality.PairRoot

namespace Thesis
namespace Causality

universe u

variable {S : ObservedSignature.{u}}

open PathSpecification

/-!
# A simple observed-endpoint path uses each original pair root at most once

The executable separation graph contains both labels `latentPair i j` and
`latentPair j i`.  They have the same two observed children and represent one
original bidirected pair.  An installed mechanism has just the one reserved
root for that pair, not a separate independent bit for each expanded label.

Along a simple path with observed endpoints, every latent-pair occurrence is
internal.  Its two immediate neighbours are the pair's distinct observed
endpoints.  Neither endpoint occurs elsewhere in the simple list.  The other
label therefore cannot be entered in the earlier prefix or left in the later
suffix.  This proves alias exclusion from actual adjacency and simplicity;
it is not an extra independence assumption of the countermodel construction.

The later mask construction can consequently identify reversed labels with
the same real reserved input without duplicating that input along the path.
No path search, exponential enumeration, choice or propositional excluded
middle is used in this graph-to-input bridge.
-/

namespace PathSpecification

/-- A neighbour of a latent-pair vertex is one of its two actual observed
children, and the original bidirected pair really exists.  There are no
incoming arrows to a latent vertex, even after graph mutilation. -/
theorem Adjacent.latentPair_children {G : ObservedGraph S} {m : GraphMutilation S}
    {left right : Fin S.count} {neighbor : SeparationNode S}
    (adjacent : Adjacent G m (.latentPair left right) neighbor) :
    (neighbor = .observed left ∨ neighbor = .observed right) ∧ G.bidirected left right = true := by
  cases neighbor with
  | latentPair first second => rcases adjacent with impossible | impossible <;> cases impossible
  | observed child =>
      rcases adjacent with actual | impossible
      · have parts := Bool.and_eq_true_iff.mp actual
        have pairParts := Bool.and_eq_true_iff.mp parts.1
        have endpoints := Bool.or_eq_true_iff.mp pairParts.2
        constructor
        · rcases endpoints with same | same
          · exact Or.inl (congrArg SeparationNode.observed ((finBeq_eq_true_iff child left).mp same))
          · exact Or.inr (congrArg SeparationNode.observed ((finBeq_eq_true_iff child right).mp same))
        · exact pairParts.1
      · cases impossible

private theorem consecutive_left {α : Type _} {relation : α -> α -> Prop} (before after : List α)
    (consecutive : Consecutive relation (before ++ after)) : Consecutive relation before := by
  induction before with
  | nil => exact True.intro
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil => exact True.intro
      | cons next rest => exact ⟨consecutive.1, inductionHypothesis consecutive.2⟩

/-- A connected list cannot enter a specified latent pair if neither of its
observed children is in the list and its initial vertex is not that pair. -/
private theorem no_latentPair_without_children {G : ObservedGraph S} {m : GraphMutilation S}
    (left right : Fin S.count) (head : SeparationNode S) (tail : List (SeparationNode S))
    (initial : head ≠ .latentPair left right)
    (adjacent : Consecutive (Adjacent G m) (head :: tail))
    (noLeft : .observed left ∉ head :: tail) (noRight : .observed right ∉ head :: tail) :
    .latentPair left right ∉ head :: tail := by
  induction tail generalizing head with
  | nil =>
      intro member
      have same := List.mem_singleton.mp member
      exact initial same.symm
  | cons next rest inductionHypothesis =>
      have nextDifferent : next ≠ .latentPair left right := by
        intro same
        have neighbors := (same ▸ adjacent.1).symm.latentPair_children
        rcases neighbors.1 with incident | incident
        · exact noLeft (List.mem_cons.mpr (Or.inl incident.symm))
        · exact noRight (List.mem_cons.mpr (Or.inl incident.symm))
      have tailNoLeft : .observed left ∉ next :: rest := fun member => noLeft (List.mem_cons_of_mem head member)
      have tailNoRight : .observed right ∉ next :: rest := fun member => noRight (List.mem_cons_of_mem head member)
      intro member
      rcases List.mem_cons.mp member with same | later
      · exact initial same.symm
      · exact inductionHypothesis next nextDifferent adjacent.2 tailNoLeft tailNoRight later

/-- The actual latent window consumes both of its distinct observed children.
Simplicity excludes those children from the earlier prefix; adjacency then
prevents that prefix from entering the reversed alias.  The suffix will be
handled by replaying this same argument on the reversed active path. -/
private theorem alias_not_before_window {G : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath G m given (.observed source) (.observed target))
    (before after : List (SeparationNode S)) (previous next : SeparationNode S)
    (left right : Fin S.count)
    (window : path.nodes = before ++ previous :: .latentPair left right :: next :: after) :
    .latentPair right left ∉ before := by
  have consecutive : Consecutive (Adjacent G m)
      (before ++ previous :: .latentPair left right :: next :: after) := window ▸ path.adjacent
  have simple : (before ++ previous :: .latentPair left right :: next :: after).Nodup := window ▸ path.simple
  have previousChildren := (Consecutive.pair_of_append before (next :: after) previous (.latentPair left right) consecutive).symm.latentPair_children
  have nextChildren := (Consecutive.pair_of_append (relation := Adjacent G m) (before ++ [previous]) after (.latentPair left right) next
    (by simpa only [List.append_assoc, List.singleton_append] using consecutive)).latentPair_children
  have previousNotNext : previous ≠ next := by
    have tailSimple := (List.nodup_append.mp simple).2.1
    have unique := (List.nodup_cons.mp tailSimple).1
    intro same
    exact unique (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl same)))
  -- Distinct immediate neighbours must exhaust the pair's two children.
  -- This uses actual list simplicity, not an ordering convention for roots.
  have endpoints : (previous = .observed left ∧ next = .observed right) ∨
      (previous = .observed right ∧ next = .observed left) := by
    rcases previousChildren.1 with previousLeft | previousRight
    · rcases nextChildren.1 with nextLeft | nextRight
      · exact False.elim (previousNotNext (previousLeft.trans nextLeft.symm))
      · exact Or.inl ⟨previousLeft, nextRight⟩
    · rcases nextChildren.1 with nextLeft | nextRight
      · exact Or.inr ⟨previousRight, nextLeft⟩
      · exact False.elim (previousNotNext (previousRight.trans nextRight.symm))
  have noPrevious : previous ∉ before := by
    intro member
    exact (List.nodup_append.mp simple).2.2 previous member previous (List.mem_cons.mpr (Or.inl rfl)) rfl
  have noNext : next ∉ before := by
    intro member
    exact (List.nodup_append.mp simple).2.2 next member next
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl)))) rfl
  have noLeft : .observed left ∉ before := by
    rcases endpoints with ordered | reversed
    · simpa only [ordered.1] using noPrevious
    · simpa only [reversed.2] using noNext
  have noRight : .observed right ∉ before := by
    rcases endpoints with ordered | reversed
    · simpa only [ordered.2] using noNext
    · simpa only [reversed.1] using noPrevious
  cases shape : before with
  | nil => exact List.not_mem_nil
  | cons head tail =>
      have starts := path.starts
      rw [window, shape, List.cons_append, List.head?_cons] at starts
      have headObserved : head = .observed source := Option.some.inj starts
      have headDifferent : head ≠ .latentPair right left := by rw [headObserved]; intro impossible; cases impossible
      have earlier := consecutive_left before (previous :: .latentPair left right :: next :: after) consecutive
      rw [shape] at earlier noLeft noRight
      exact no_latentPair_without_children right left head tail headDifferent earlier noRight noLeft

/-- Every latent-pair occurrence names an actual original bidirected edge.
The existence of immediate neighbours is used only propositionally; no
concrete input or path is selected from an existential proof. -/
theorem ActivePath.latentPair_is_bidirected {G : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath G m given (.observed source) (.observed target))
    (left right : Fin S.count) (member : .latentPair left right ∈ path.nodes) : G.bidirected left right = true := by
  rcases exists_internal_neighbors_of_mem path.starts path.finishes member (by intro impossible; cases impossible)
    (by intro impossible; cases impossible) with ⟨before, previous, next, after, window⟩
  have adjacent := Consecutive.pair_of_append before (next :: after) previous (.latentPair left right) (window ▸ path.adjacent)
  exact adjacent.symm.latentPair_children.2

/-- Two expanded labels for the same original pair cannot both occur on
this simple observed-endpoint path.  This is valid for any active path, not
only one found by a particular search or already in a collider normal form. -/
theorem ActivePath.latentPair_swap_not_mem {G : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath G m given (.observed source) (.observed target))
    (left right : Fin S.count) (member : .latentPair left right ∈ path.nodes) :
    .latentPair right left ∉ path.nodes := by
  rcases exists_internal_neighbors_of_mem path.starts path.finishes member (by intro impossible; cases impossible)
    (by intro impossible; cases impossible) with ⟨before, previous, next, after, window⟩
  have noBefore := alias_not_before_window path before after previous next left right window
  -- Reversal keeps observed endpoints and simplicity.  It therefore excludes
  -- the alias from the later suffix without introducing a second path search.
  have reversedWindow : path.reverse.nodes = after.reverse ++ next :: .latentPair left right :: previous :: before.reverse := by
    change path.nodes.reverse = _
    rw [window]
    simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
  have noAfterReverse := alias_not_before_window path.reverse after.reverse before.reverse next previous left right reversedWindow
  have edge := path.latentPair_is_bidirected left right member
  have different : .latentPair right left ≠ (SeparationNode.latentPair left right : SeparationNode S) := by
    intro same
    have endpoints := SeparationNode.latentPair.inj same
    have equal : right = left := endpoints.1
    subst right
    rw [G.bidirected_irreflexive] at edge
    cases edge
  intro other
  rw [window] at other
  rcases List.mem_append.mp other with earlier | rest
  · exact noBefore earlier
  · rcases List.mem_cons.mp rest with same | rest
    · have children := (Consecutive.pair_of_append before (next :: after) previous (.latentPair left right)
        (window ▸ path.adjacent)).symm.latentPair_children
      rcases children.1 with observed | observed <;> rw [observed] at same <;> cases same
    · rcases List.mem_cons.mp rest with same | rest
      · exact different same
      · rcases List.mem_cons.mp rest with same | later
        · have children := (Consecutive.pair_of_append (relation := Adjacent G m) (before ++ [previous]) after (.latentPair left right) next
            (by simpa only [List.append_assoc, List.singleton_append] using window ▸ path.adjacent)).latentPair_children
          rcases children.1 with observed | observed <;> rw [observed] at same <;> cases same
        · exact noAfterReverse (List.mem_reverse.mpr later)

end PathSpecification

namespace SeparationNode

/-- The ordered label of the same expanded pair.  Only the finite ranks
are compared; this does not choose a new latent input or alter an observed
vertex.  Inactive equal-endpoint labels also have a well-defined image. -/
def canonicalPair : SeparationNode S -> SeparationNode S
  | .observed child => .observed child
  | .latentPair left right => if left.val < right.val then .latentPair left right else .latentPair right left

private theorem canonicalPair_eq_labels (left right : SeparationNode S)
    (same : left.canonicalPair = right.canonicalPair) :
    right = left ∨ Exists fun first : Fin S.count => Exists fun second : Fin S.count =>
      left = .latentPair first second ∧ right = .latentPair second first := by
  cases left with
  | observed child =>
      cases right with
      | observed other => exact Or.inl same.symm
      | latentPair first second =>
          by_cases ordered : first.val < second.val
          · simp only [canonicalPair, if_pos ordered] at same; cases same
          · simp only [canonicalPair, if_neg ordered] at same; cases same
  | latentPair first second =>
      cases right with
      | observed child =>
          by_cases ordered : first.val < second.val
          · simp only [canonicalPair, if_pos ordered] at same; cases same
          · simp only [canonicalPair, if_neg ordered] at same; cases same
      | latentPair otherFirst otherSecond =>
          by_cases ordered : first.val < second.val
          · by_cases otherOrdered : otherFirst.val < otherSecond.val
            · simp only [canonicalPair, if_pos ordered, if_pos otherOrdered] at same
              exact Or.inl same.symm
            · simp only [canonicalPair, if_pos ordered, if_neg otherOrdered] at same
              rcases SeparationNode.latentPair.inj same with ⟨sameFirst, sameSecond⟩
              subst otherFirst
              subst otherSecond
              exact Or.inr ⟨first, second, rfl, rfl⟩
          · by_cases otherOrdered : otherFirst.val < otherSecond.val
            · simp only [canonicalPair, if_neg ordered, if_pos otherOrdered] at same
              rcases SeparationNode.latentPair.inj same with ⟨sameFirst, sameSecond⟩
              subst otherFirst
              subst otherSecond
              exact Or.inr ⟨first, second, rfl, rfl⟩
            · simp only [canonicalPair, if_neg ordered, if_neg otherOrdered] at same
              rcases SeparationNode.latentPair.inj same with ⟨sameFirst, sameSecond⟩
              subst otherFirst
              subst otherSecond
              exact Or.inl rfl

end SeparationNode

namespace PathSpecification

/-- Canonical pair labels are injective on the actual path vertices, even
though the map is deliberately not injective on the whole expanded graph.
Alias exclusion supplies the missing graph-specific injectivity theorem. -/
theorem ActivePath.canonicalPair_injective_on_nodes {G : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath G m given (.observed source) (.observed target))
    (left right : SeparationNode S) (leftMember : left ∈ path.nodes) (rightMember : right ∈ path.nodes)
    (same : left.canonicalPair = right.canonicalPair) : left = right := by
  rcases SeparationNode.canonicalPair_eq_labels left right same with identical | ⟨first, second, leftEq, rightEq⟩
  · exact identical.symm
  · subst left
    subst right
    exact False.elim (path.latentPair_swap_not_mem first second leftMember rightMember)

private theorem map_nodup_on_members {α β : Type _} (mapping : α -> β) (nodes : List α)
    (simple : nodes.Nodup)
    (injective : forall left right, left ∈ nodes -> right ∈ nodes -> mapping left = mapping right -> left = right) :
    (nodes.map mapping).Nodup := by
  induction nodes with
  | nil => exact List.nodup_nil
  | cons head tail inductionHypothesis =>
      have parts := List.nodup_cons.mp simple
      apply List.nodup_cons.mpr
      constructor
      · intro member
        rcases List.mem_map.mp member with ⟨other, listed, equal⟩
        have same := injective other head (List.mem_cons_of_mem _ listed) (List.mem_cons.mpr (Or.inl rfl)) equal
        subst other
        exact parts.1 listed
      · exact inductionHypothesis parts.2 (fun left right leftMem rightMem same =>
          injective left right (List.mem_cons_of_mem _ leftMem) (List.mem_cons_of_mem _ rightMem) same)

/-- Mapping the actual vertices to their canonical pair labels preserves
simplicity.  No duplicate root is silently erased from an interaction fold. -/
theorem ActivePath.canonicalPair_nodes_nodup {G : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath G m given (.observed source) (.observed target)) :
    (path.nodes.map SeparationNode.canonicalPair).Nodup :=
  map_nodup_on_members _ path.nodes path.simple path.canonicalPair_injective_on_nodes

/-! ## Name and certify the original reserved input, rather than an alias -/

/-- The actual original pair-root index of a latent vertex on this path.
The finite ordered pair lookup returns data in `Type`; its edge certificate
is proved from path adjacency above, not extracted by choice. -/
def ActivePath.pairRootOfLatent {G : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath G m given (.observed source) (.observed target))
    (left right : Fin S.count) (member : .latentPair left right ∈ path.nodes) : Fin (pairRootCount G) :=
  pairRootBetween G (path.latentPair_is_bidirected left right member)

/-- The selected original root has exactly the canonical label of the
path occurrence.  A reversed expanded label selects the same stored pair. -/
theorem ActivePath.pairRootOfLatent_label {G : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath G m given (.observed source) (.observed target))
    (left right : Fin S.count) (member : .latentPair left right ∈ path.nodes) :
    .latentPair ((pairRoots G).get (path.pairRootOfLatent left right member)).1
      ((pairRoots G).get (path.pairRootOfLatent left right member)).2 =
        (SeparationNode.latentPair left right).canonicalPair := by
  by_cases ordered : left.val < right.val
  · simp only [pairRootOfLatent, pairRootBetween, SeparationNode.canonicalPair, dif_pos ordered, if_pos ordered]
    rw [pairRoots_get_of]
  · simp only [pairRootOfLatent, pairRootBetween, SeparationNode.canonicalPair, dif_neg ordered, if_neg ordered]
    rw [pairRoots_get_of]

/-- The input selected from the path is available at its actual left child;
it is not a new global switching bit read by unrelated mechanisms. -/
theorem ActivePath.pairRootOfLatent_incident_left {G : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath G m given (.observed source) (.observed target))
    (left right : Fin S.count) (member : .latentPair left right ∈ path.nodes) :
    pairRootIncident G (path.pairRootOfLatent left right member) left = true :=
  pairRootIncident_between_left G (path.latentPair_is_bidirected left right member)

/-- The same original input is also available at its actual right child. -/
theorem ActivePath.pairRootOfLatent_incident_right {G : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath G m given (.observed source) (.observed target))
    (left right : Fin S.count) (member : .latentPair left right ∈ path.nodes) :
    pairRootIncident G (path.pairRootOfLatent left right member) right = true :=
  pairRootIncident_between_right G (path.latentPair_is_bidirected left right member)

/-- Distinct latent occurrences on the actual path cannot select the same
original reserved input.  This is stronger than simplicity of expanded
labels: it rules out duplicated input indices after identifying both aliases. -/
theorem ActivePath.pairRootOfLatent_injective {G : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath G m given (.observed source) (.observed target))
    (left right otherLeft otherRight : Fin S.count)
    (member : .latentPair left right ∈ path.nodes) (otherMember : .latentPair otherLeft otherRight ∈ path.nodes)
    (same : path.pairRootOfLatent left right member = path.pairRootOfLatent otherLeft otherRight otherMember) :
    left = otherLeft ∧ right = otherRight := by
  have labels := congrArg (fun root => SeparationNode.latentPair ((pairRoots G).get root).1 ((pairRoots G).get root).2) same
  dsimp only at labels
  rw [path.pairRootOfLatent_label left right member, path.pairRootOfLatent_label otherLeft otherRight otherMember] at labels
  exact SeparationNode.latentPair.inj (path.canonicalPair_injective_on_nodes _ _ member otherMember labels)

end PathSpecification
end Causality
end Thesis
