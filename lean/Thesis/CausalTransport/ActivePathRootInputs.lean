import Thesis.CausalTransport.ActivePathBoundary
import Thesis.Causality.PairRootUniqueness

namespace Thesis
namespace Causality

universe u

open PathSpecification

/-!
# Original reserved inputs at the actual neighbours of a path row

The global head-phase conservation theorem cancels every used root at its
two children.  Local parity requires more: at a particular row we must know
*which* incoming path neighbours supply its reserved-input reads.  The
theorems here connect the executable root mask to those actual neighbours,
including a reversed expanded label, without introducing an independent
input for that label.

`rootAt` compares canonical labels in the original graph's literal root
enumeration.  The enumeration's proved uniqueness identifies its index with
the path's actual lookup.  For an internal observed window, the root mask is
exactly the XOR of the two incoming-neighbour entries.  Simplicity and alias
exclusion prove that these entries cannot both name the same original root.
This graph-only layer does not assume a row parity, a sample assignment,
or a semantic countermodel certificate.
-/

variable {S : ObservedSignature.{u}}

namespace ActivePathInput

/-! ## Recognize a neighbour's original input, retaining its actual index -/

/-- Test whether an expanded neighbour names this original reserved root.
Observed neighbours never name a root.  The two latent aliases are compared
after canonicalization, rather than treated as independent coordinates. -/
def rootAt (graph : ObservedGraph S) (root : Fin (pairRootCount graph))
    (neighbor : SeparationNode S) : Bool :=
  SeparationNode.beq
    (.latentPair ((pairRoots graph).get root).1 ((pairRoots graph).get root).2)
    neighbor.canonicalPair

/-- The canonical comparison recognizes exactly the stored pair's two
expanded labels, not an unrelated or inactive pair. -/
theorem rootAt_eq_true_iff (graph : ObservedGraph S) (root : Fin (pairRootCount graph))
    (neighbor : SeparationNode S) :
    rootAt graph root neighbor = true ↔
      neighbor = .latentPair ((pairRoots graph).get root).1 ((pairRoots graph).get root).2 ∨
      neighbor = .latentPair ((pairRoots graph).get root).2 ((pairRoots graph).get root).1 := by
  rw [rootAt, SeparationNode.beq_eq_true_iff]
  have ordered := (pairRoots_get_spec graph root).1
  have reverseNotOrdered : ¬ ((pairRoots graph).get root).2.val < ((pairRoots graph).get root).1.val :=
    Nat.not_lt_of_ge (Nat.le_of_lt ordered)
  constructor
  · intro equal
    cases neighbor with
    | observed child => cases equal
    | latentPair left right =>
        by_cases forward : left.val < right.val
        · simp only [SeparationNode.canonicalPair, if_pos forward] at equal
          exact Or.inl equal.symm
        · simp only [SeparationNode.canonicalPair, if_neg forward] at equal
          have ends := SeparationNode.latentPair.inj equal
          have leftEq := ends.2.symm
          have rightEq := ends.1.symm
          rw [leftEq, rightEq]
          exact Or.inr rfl
  · intro alias
    rcases alias with equal | equal
    · rw [equal, SeparationNode.canonicalPair, if_pos ordered]
    · rw [equal, SeparationNode.canonicalPair, if_neg reverseNotOrdered]

/-- An observed path neighbour does not contribute a reserved input. -/
theorem rootAt_observed (graph : ObservedGraph S) (root : Fin (pairRootCount graph))
    (child : Fin S.count) : rootAt graph root (.observed child) = false := by
  apply Bool.eq_false_iff.mpr
  intro impossible
  have labels := (rootAt_eq_true_iff graph root (.observed child)).mp impossible
  rcases labels with impossible | impossible <;> cases impossible

/-- A latent occurrence recognizes exactly its actual original lookup
index.  Uniqueness is proved for the entire root enumeration, not supplied
as an extra injectivity premise at this row. -/
theorem rootAt_latent_eq_index {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (left right : Fin S.count) (member : .latentPair left right ∈ path.nodes)
    (root : Fin (pairRootCount graph)) :
    rootAt graph root (.latentPair left right) = decide (root = path.pairRootOfLatent left right member) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro selected
    have label := (SeparationNode.beq_eq_true_iff _ _).mp selected
    have actualLabel := path.pairRootOfLatent_label left right member
    have ends := SeparationNode.latentPair.inj (label.trans actualLabel.symm)
    exact pairRoots_get_injective graph root _ (Prod.ext ends.1 ends.2)
  · intro equal
    subst root
    exact (SeparationNode.beq_eq_true_iff _ _).mpr (path.pairRootOfLatent_label left right member)

/-! ## Incidence becomes an actual incoming step at each original child -/

private theorem latent_edge_of_adjacent {graph : ObservedGraph S} {m : GraphMutilation S}
    {left right : Fin S.count} {neighbor : SeparationNode S}
    (adjacent : Adjacent graph m (.latentPair left right) neighbor) :
    graph.expandedMutilatedEdge m (.latentPair left right) neighbor = true := by
  rcases adjacent with forward | backward
  · exact forward
  · cases neighbor <;> cases backward

/-- Both original children are actual incoming neighbours of their latent
occurrence.  This strengthens head membership: it identifies the very edge
whose input the local signal reads.  A simple observed-endpoint path cannot
enter and leave a latent root through the same child. -/
theorem latentPair_children_are_incoming {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (left right : Fin S.count) (member : .latentPair left right ∈ path.nodes) :
    incomingEdge graph m path.nodes (.latentPair left right) left = true ∧
      incomingEdge graph m path.nodes (.latentPair left right) right = true := by
  rcases exists_internal_neighbors_of_mem path.starts path.finishes member
    (by intro impossible; cases impossible) (by intro impossible; cases impossible) with
      ⟨before, previous, next, after, window⟩
  have consecutive := window ▸ path.adjacent
  have first := (Consecutive.pair_of_append before (next :: after) previous (.latentPair left right) consecutive).symm
  have second := Consecutive.pair_of_append (relation := Adjacent graph m) (before ++ [previous]) after
    (.latentPair left right) next (by simpa only [List.append_assoc, List.singleton_append] using consecutive)
  have different : previous ≠ next := by
    have simple := (List.nodup_append.mp (window ▸ path.simple)).2.1
    have unique := (List.nodup_cons.mp simple).1
    intro equal
    exact unique (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl equal)))
  have atPrevious : forall child, previous = .observed child ->
      incomingEdge graph m path.nodes (.latentPair left right) child = true := by
    intro child equal
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply (stepOnPath_eq_true_iff _ _ _).mpr
      exact ⟨before, next :: after, Or.inr (by simpa only [← equal] using window)⟩
    · simpa only [equal] using latent_edge_of_adjacent first
  have atNext : forall child, next = .observed child ->
      incomingEdge graph m path.nodes (.latentPair left right) child = true := by
    intro child equal
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply (stepOnPath_eq_true_iff _ _ _).mpr
      exact ⟨before ++ [previous], after, Or.inl (by
        simpa only [List.append_assoc, List.singleton_append, ← equal] using window)⟩
    · simpa only [equal] using latent_edge_of_adjacent second
  rcases first.latentPair_children.1 with previousLeft | previousRight
  · rcases second.latentPair_children.1 with nextLeft | nextRight
    · exact False.elim (different (previousLeft.trans nextLeft.symm))
    · exact ⟨atPrevious left previousLeft, atNext right nextRight⟩
  · rcases second.latentPair_children.1 with nextLeft | nextRight
    · exact ⟨atNext left nextLeft, atPrevious right previousRight⟩
    · exact False.elim (different (previousRight.trans nextRight.symm))

/-- A reserved-input mask entry is present exactly when an actual incoming
path neighbour names that input.  The reverse implication checks genuine
incidence from the kept expanded arrow; an arbitrary alias match is not
enough to grant the row access. -/
theorem pairUsed_incident_iff_incoming {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (root : Fin (pairRootCount graph)) (child : Fin S.count) :
    (pairUsed graph path.nodes root && pairRootIncident graph root child) = true ↔
      Exists fun neighbor : SeparationNode S =>
        rootAt graph root neighbor = true ∧ incomingEdge graph m path.nodes neighbor child = true := by
  constructor
  · intro selected
    have entries := Bool.and_eq_true_iff.mp selected
    rcases (pairUsed_eq_true_iff graph path.nodes root).mp entries.1 with ordered | reversed
    · have arrows := latentPair_children_are_incoming path _ _ ordered
      refine ⟨_, (rootAt_eq_true_iff graph root _).mpr (Or.inl rfl), ?_⟩
      rcases (pairRootIncident_iff graph root child).mp entries.2 with left | right
      · simpa only [left] using arrows.1
      · simpa only [right] using arrows.2
    · have arrows := latentPair_children_are_incoming path _ _ reversed
      refine ⟨_, (rootAt_eq_true_iff graph root _).mpr (Or.inr rfl), ?_⟩
      rcases (pairRootIncident_iff graph root child).mp entries.2 with left | right
      · simpa only [left] using arrows.2
      · simpa only [right] using arrows.1
  · rintro ⟨neighbor, selected, incoming⟩
    have entries := Bool.and_eq_true_iff.mp incoming
    have member := (stepOnPath_members entries.1).1
    rcases (rootAt_eq_true_iff graph root neighbor).mp selected with ordered | reversed
    · subst neighbor
      apply Bool.and_eq_true_iff.mpr
      refine ⟨(pairUsed_eq_true_iff graph path.nodes root).mpr (Or.inl member), ?_⟩
      have endpoints := Bool.or_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp entries.2).1).2
      apply (pairRootIncident_iff graph root child).mpr
      rcases endpoints with left | right
      · exact Or.inl ((finBeq_eq_true_iff _ _).mp left)
      · exact Or.inr ((finBeq_eq_true_iff _ _).mp right)
    · subst neighbor
      apply Bool.and_eq_true_iff.mpr
      refine ⟨(pairUsed_eq_true_iff graph path.nodes root).mpr (Or.inr member), ?_⟩
      have endpoints := (Bool.or_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp entries.2).1).2)
      apply (pairRootIncident_iff graph root child).mpr
      rcases endpoints with right | left
      · exact Or.inr ((finBeq_eq_true_iff _ _).mp right)
      · exact Or.inl ((finBeq_eq_true_iff _ _).mp left)

/-! ## Account for every reserved read in an internal observed window -/

/-- An internal observed row reads only its two actual incoming
neighbours.  The scan's disjunction is an XOR because the simple window
has distinct neighbours; this form is suited to finite local input folds. -/
theorem incomingEdge_internal_window {nodes : List (SeparationNode S)} (simple : nodes.Nodup)
    (graph : ObservedGraph S) (m : GraphMutilation S)
    (before after : List (SeparationNode S)) (previous next parent : SeparationNode S)
    (child : Fin S.count) (window : nodes = before ++ previous :: .observed child :: next :: after) :
    incomingEdge graph m nodes parent child =
      Bool.xor (SeparationNode.beq parent previous && graph.expandedMutilatedEdge m parent (.observed child))
        (SeparationNode.beq parent next && graph.expandedMutilatedEdge m parent (.observed child)) := by
  have neighbors : stepOnPath parent (.observed child) nodes =
      (SeparationNode.beq parent previous || SeparationNode.beq parent next) := by
    apply Bool.eq_iff_iff.mpr
    rw [stepOnPath_internal_window simple before after previous (.observed child) next parent window,
      Bool.or_eq_true_iff, SeparationNode.beq_eq_true_iff, SeparationNode.beq_eq_true_iff]
  have different : previous ≠ next := by
    have unique := (List.nodup_cons.mp (List.nodup_append.mp (window ▸ simple)).2.1).1
    intro equal
    exact unique (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl equal)))
  have cannotBoth : ¬ (SeparationNode.beq parent previous = true ∧ SeparationNode.beq parent next = true) := by
    intro both
    have first := (SeparationNode.beq_eq_true_iff _ _).mp both.1
    have second := (SeparationNode.beq_eq_true_iff _ _).mp both.2
    exact different (first.symm.trans second)
  unfold incomingEdge
  rw [neighbors]
  cases first : SeparationNode.beq parent previous <;> cases second : SeparationNode.beq parent next
  · rfl
  · simp only [Bool.false_or, Bool.true_and, Bool.false_and, Bool.false_xor]
  · simp only [Bool.or_false, Bool.true_and, Bool.false_and, Bool.xor_false]
  · exact False.elim (cannotBoth ⟨first, second⟩)

/-- On the actual simple path, two neighbours naming the same original
input are the same expanded occurrence.  This uses alias exclusion, not
just inequality of the two stored endpoint labels. -/
theorem rootAt_injective_on_path {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (root : Fin (pairRootCount graph)) (left right : SeparationNode S)
    (leftMember : left ∈ path.nodes) (rightMember : right ∈ path.nodes)
    (leftInput : rootAt graph root left = true) (rightInput : rootAt graph root right = true) : left = right := by
  have first := (SeparationNode.beq_eq_true_iff _ _).mp leftInput
  have second := (SeparationNode.beq_eq_true_iff _ _).mp rightInput
  exact path.canonicalPair_injective_on_nodes left right leftMember rightMember (first.symm.trans second)

/-- The actual reserved-input mask at an internal row is precisely the
XOR of its two incoming-neighbour entries.  There cannot be two reads of
one original root: the immediate neighbours are distinct, and their
canonical labels are injective on the stored path.  The result applies
even when one or both neighbours are observed, where `rootAt` is false. -/
theorem pairUsed_incident_internal_window {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (before after : List (SeparationNode S)) (previous next : SeparationNode S)
    (child : Fin S.count) (window : path.nodes = before ++ previous :: .observed child :: next :: after)
    (root : Fin (pairRootCount graph)) :
    (pairUsed graph path.nodes root && pairRootIncident graph root child) =
      Bool.xor (rootAt graph root previous && graph.expandedMutilatedEdge m previous (.observed child))
        (rootAt graph root next && graph.expandedMutilatedEdge m next (.observed child)) := by
  have actualOr : (pairUsed graph path.nodes root && pairRootIncident graph root child) =
      ((rootAt graph root previous && graph.expandedMutilatedEdge m previous (.observed child)) ||
        (rootAt graph root next && graph.expandedMutilatedEdge m next (.observed child))) := by
    apply Bool.eq_iff_iff.mpr
    rw [pairUsed_incident_iff_incoming path, Bool.or_eq_true_iff,
      Bool.and_eq_true_iff, Bool.and_eq_true_iff]
    constructor
    · rintro ⟨neighbor, input, incoming⟩
      have entries := Bool.and_eq_true_iff.mp incoming
      rcases (stepOnPath_internal_window path.simple before after previous (.observed child) next neighbor window).mp
        entries.1 with equal | equal
      · exact Or.inl ⟨equal ▸ input, equal ▸ entries.2⟩
      · exact Or.inr ⟨equal ▸ input, equal ▸ entries.2⟩
    · intro found
      rcases found with previousEntry | nextEntry
      · refine ⟨previous, previousEntry.1, Bool.and_eq_true_iff.mpr ⟨?_, previousEntry.2⟩⟩
        exact (stepOnPath_internal_window path.simple before after previous (.observed child) next previous window).mpr
          (Or.inl rfl)
      · refine ⟨next, nextEntry.1, Bool.and_eq_true_iff.mpr ⟨?_, nextEntry.2⟩⟩
        exact (stepOnPath_internal_window path.simple before after previous (.observed child) next next window).mpr
          (Or.inr rfl)
  rw [actualOr]
  have different : previous ≠ next := by
    have simple := (List.nodup_append.mp (window ▸ path.simple)).2.1
    have unique := (List.nodup_cons.mp simple).1
    intro equal
    exact unique (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl equal)))
  have cannotBoth : ¬ (rootAt graph root previous = true ∧ rootAt graph root next = true) := by
    intro both
    apply different
    apply rootAt_injective_on_path path root previous next
      (window ▸ List.mem_append_right before List.mem_cons_self)
      (window ▸ List.mem_append_right before (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      both.1 both.2
  cases first : rootAt graph root previous <;> cases second : rootAt graph root next
  · rfl
  · simp only [Bool.false_and, Bool.false_or, Bool.false_xor]
  · simp only [Bool.false_and, Bool.or_false, Bool.xor_false]
  · exact False.elim (cannotBoth ⟨first, second⟩)

end ActivePathInput

end Causality
end Thesis
