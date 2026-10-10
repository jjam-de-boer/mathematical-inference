import Thesis.CausalTransport.ActivePathPairRoots

namespace Thesis
namespace Causality

universe u

open PathSpecification

/-!
# Select actual incoming path edges and original reserved roots

These executable finite scans use only the supplied active-path list and the
exact mutilated graph.  They select observed heads, kept observed arrows,
and the original pair-root indices of latent occurrences.  An observed fork
with no incoming path arrow contributes no selected own row.  Both children
of every used original root are actual incoming heads and are not cut.

The graph layer is independent of signal, probability, and hedge installation.
It works for any observed-signature universe and uses the original graph's
root enumeration.  The binary installation has definitionally the same root
metadata; no new latent coordinates or representatives are chosen here.

`HedgeChannelPathInputs` separately installs these selections in legal local
signals and proves conservation of their actual homogeneous phases.  The
observed boundary computed below is not assumed to be an outcome character:
`ActivePathBoundary` proves its endpoint/collider form from actual windows,
while installing the real collider activations remains separate graph work.
-/

variable {S : ObservedSignature.{u}}

namespace ActivePathInput

/-- Test actual consecutive occurrences, allowing either list orientation.
The recursion scans only the supplied list; it does not search the expanded
graph or enumerate assignments.  Arrow orientation is checked separately. -/
def stepOnPath (left right : SeparationNode S) : List (SeparationNode S) -> Bool
  | first :: second :: rest =>
      ((SeparationNode.beq first left && SeparationNode.beq second right) ||
        (SeparationNode.beq first right && SeparationNode.beq second left)) ||
          stepOnPath left right (second :: rest)
  | _ => false

/-- The scan reports exactly a displayed consecutive pair in one of the
two list orientations.  The decomposition is used propositionally only. -/
theorem stepOnPath_eq_true_iff (left right : SeparationNode S) (nodes : List (SeparationNode S)) :
    stepOnPath left right nodes = true ↔
      Exists fun before : List (SeparationNode S) => Exists fun after : List (SeparationNode S) =>
        nodes = before ++ left :: right :: after ∨ nodes = before ++ right :: left :: after := by
  induction nodes with
  | nil =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨before, after, window | window⟩ <;>
          have lengths := congrArg List.length window <;>
          simp only [List.length_nil, List.length_append, List.length_cons] at lengths <;> omega
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          constructor
          · intro impossible; cases impossible
          · rintro ⟨before, after, window | window⟩ <;>
              have lengths := congrArg List.length window <;>
              simp only [List.length_nil, List.length_append, List.length_cons] at lengths <;> omega
      | cons second rest =>
          rw [stepOnPath, Bool.or_eq_true_iff, Bool.or_eq_true_iff]
          constructor
          · intro found
            rcases found with (forward | backward) | later
            · have ends := Bool.and_eq_true_iff.mp forward
              have firstEq := (SeparationNode.beq_eq_true_iff first left).mp ends.1
              have secondEq := (SeparationNode.beq_eq_true_iff second right).mp ends.2
              subst first
              subst second
              exact ⟨[], rest, Or.inl rfl⟩
            · have ends := Bool.and_eq_true_iff.mp backward
              have firstEq := (SeparationNode.beq_eq_true_iff first right).mp ends.1
              have secondEq := (SeparationNode.beq_eq_true_iff second left).mp ends.2
              subst first
              subst second
              exact ⟨[], rest, Or.inr rfl⟩
            · rcases inductionHypothesis.mp later with ⟨before, after, forward | backward⟩
              · exact ⟨first :: before, after, Or.inl (congrArg (List.cons first) forward)⟩
              · exact ⟨first :: before, after, Or.inr (congrArg (List.cons first) backward)⟩
          · rintro ⟨before, after, window⟩
            cases before with
            | nil =>
                rcases window with forward | backward
                · have ends := List.cons.inj forward
                  have firstEq := ends.1
                  have secondEq := (List.cons.inj ends.2).1
                  subst first
                  subst second
                  exact Or.inl (Or.inl (Bool.and_eq_true_iff.mpr
                    ⟨(SeparationNode.beq_eq_true_iff _ _).mpr rfl, (SeparationNode.beq_eq_true_iff _ _).mpr rfl⟩))
                · have ends := List.cons.inj backward
                  have firstEq := ends.1
                  have secondEq := (List.cons.inj ends.2).1
                  subst first
                  subst second
                  exact Or.inl (Or.inr (Bool.and_eq_true_iff.mpr
                    ⟨(SeparationNode.beq_eq_true_iff _ _).mpr rfl, (SeparationNode.beq_eq_true_iff _ _).mpr rfl⟩))
            | cons head before =>
                apply Or.inr
                apply inductionHypothesis.mpr
                rcases window with forward | backward
                · exact ⟨before, after, Or.inl (List.cons.inj forward).2⟩
                · exact ⟨before, after, Or.inr (List.cons.inj backward).2⟩

/-- Every reported pair really occurs in the supplied list. -/
theorem stepOnPath_members {left right : SeparationNode S} {nodes : List (SeparationNode S)}
    (selected : stepOnPath left right nodes = true) : left ∈ nodes ∧ right ∈ nodes := by
  rcases (stepOnPath_eq_true_iff left right nodes).mp selected with ⟨before, after, forward | backward⟩
  · rw [forward]
    exact ⟨List.mem_append_right _ List.mem_cons_self,
      List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · rw [backward]
    exact ⟨List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self),
      List.mem_append_right _ List.mem_cons_self⟩

/-- A selected incoming edge is both a consecutive path pair and an actual
arrow in the exact cut graph.  Off-path declared arrows are not installed. -/
def incomingEdge (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (parent : SeparationNode S) (child : Fin S.count) : Bool :=
  stepOnPath parent (.observed child) nodes && graph.expandedMutilatedEdge m parent (.observed child)

/-- Select only actual observed heads.  A collider has one row even with
two incoming path arrows; an observed fork with neither incoming is omitted. -/
def headRows (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) : NodeSet S :=
  fun child => nodes.any (fun parent => incomingEdge graph m nodes parent child)

/-- Occurrence of one original root, allowing either expanded label.  The
index is that of the original pair-root enumeration, not a path position. -/
def pairUsed (graph : ObservedGraph S) (nodes : List (SeparationNode S))
    (root : Fin (pairRootCount graph)) : Bool :=
  let pair := (pairRoots graph).get root
  nodes.any (fun node => SeparationNode.beq node (.latentPair pair.1 pair.2)) ||
    nodes.any (fun node => SeparationNode.beq node (.latentPair pair.2 pair.1))

/-- The literal observed boundary of the installed head-row interaction:
one selected own row, XOR all actual outgoing path-parent reads.  Later
path-window conservation must identify this computable mask with endpoints
and colliders; it is not asserted to be the queried outcome mask already. -/
def observedBoundary (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) : NodeSet S :=
  fun coordinate => Bool.xor (headRows graph m nodes coordinate)
    ((List.finRange S.count).foldl (fun total child => Bool.xor total
      (incomingEdge graph m nodes (.observed coordinate) child)) false)

/-- The root occurrence test refers exactly to the two actual labels of
its stored original pair.  It neither chooses nor creates another root. -/
theorem pairUsed_eq_true_iff (graph : ObservedGraph S) (nodes : List (SeparationNode S))
    (root : Fin (pairRootCount graph)) :
    pairUsed graph nodes root = true ↔
      .latentPair ((pairRoots graph).get root).1 ((pairRoots graph).get root).2 ∈ nodes ∨
      .latentPair ((pairRoots graph).get root).2 ((pairRoots graph).get root).1 ∈ nodes := by
  unfold pairUsed
  rw [Bool.or_eq_true_iff, any_beq_eq_true_iff, any_beq_eq_true_iff]

/-- No head row is introduced outside the supplied path. -/
theorem headRows_member {graph : ObservedGraph S} {m : GraphMutilation S}
    {nodes : List (SeparationNode S)} {child : Fin S.count}
    (selected : headRows graph m nodes child = true) : .observed child ∈ nodes := by
  rcases List.any_eq_true.mp selected with ⟨parent, _member, incoming⟩
  exact (stepOnPath_members (Bool.and_eq_true_iff.mp incoming).1).2

/-- Every actual selected incoming input has its child row selected. -/
theorem incomingEdge_head {graph : ObservedGraph S} {m : GraphMutilation S}
    {nodes : List (SeparationNode S)} {parent : SeparationNode S} {child : Fin S.count}
    (incoming : incomingEdge graph m nodes parent child = true) : headRows graph m nodes child = true :=
  List.any_eq_true.mpr ⟨parent, (stepOnPath_members (Bool.and_eq_true_iff.mp incoming).1).1, incoming⟩

/-- An actual incoming edge, observed or latent, excludes an incoming cut
at its child.  This elementary guard is retained throughout installation. -/
theorem incomingEdge_child_not_cut {graph : ObservedGraph S} {m : GraphMutilation S}
    {parent : SeparationNode S} {child : Fin S.count}
    (edge : graph.expandedMutilatedEdge m parent (.observed child) = true) : m.removeIncoming child = false := by
  cases parent with
  | observed node => simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp edge).2
  | latentPair left right => simpa only [Bool.not_eq_true'] using (Bool.and_eq_true_iff.mp edge).2

/-- The constructed interaction-row selection avoids all incoming-cut
vertices.  No action-avoidance readiness flag is supplied by the caller. -/
theorem headRows_not_cut {graph : ObservedGraph S} {m : GraphMutilation S}
    {nodes : List (SeparationNode S)} {child : Fin S.count}
    (selected : headRows graph m nodes child = true) : m.removeIncoming child = false := by
  rcases List.any_eq_true.mp selected with ⟨parent, _member, incoming⟩
  exact incomingEdge_child_not_cut (Bool.and_eq_true_iff.mp incoming).2

private theorem latentPair_edge_of_adjacent {graph : ObservedGraph S} {m : GraphMutilation S}
    {left right : Fin S.count} {neighbor : SeparationNode S}
    (adjacent : Adjacent graph m (.latentPair left right) neighbor) :
    graph.expandedMutilatedEdge m (.latentPair left right) neighbor = true := by
  rcases adjacent with forward | backward
  · exact forward
  · cases neighbor <;> cases backward

/-- Both actual children of a latent occurrence are selected incoming
heads.  Its two immediate neighbours are distinct by path simplicity and
therefore exhaust the pair's two observed children.  An original root is
never read at an unselected fork or at a third, unrelated observed row. -/
theorem latentPair_children_are_heads {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (left right : Fin S.count) (member : .latentPair left right ∈ path.nodes) :
    headRows graph m path.nodes left = true ∧ headRows graph m path.nodes right = true := by
  rcases exists_internal_neighbors_of_mem path.starts path.finishes member
    (by intro impossible; cases impossible) (by intro impossible; cases impossible) with
      ⟨before, previous, next, after, window⟩
  have consecutive := window ▸ path.adjacent
  have first := (Consecutive.pair_of_append before (next :: after) previous (.latentPair left right) consecutive).symm
  have second := Consecutive.pair_of_append (relation := Adjacent graph m) (before ++ [previous]) after
    (.latentPair left right) next (by simpa only [List.append_assoc, List.singleton_append] using consecutive)
  have previousNotNext : previous ≠ next := by
    have simple := window ▸ path.simple
    have tailSimple := (List.nodup_append.mp simple).2.1
    have unique := (List.nodup_cons.mp tailSimple).1
    intro same
    exact unique (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl same)))
  have previousHead : forall child, previous = .observed child -> headRows graph m path.nodes child = true := by
    intro child equal
    apply List.any_eq_true.mpr
    refine ⟨.latentPair left right, member, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · apply (stepOnPath_eq_true_iff _ _ _).mpr
      exact ⟨before, next :: after, Or.inr (by simpa only [← equal] using window)⟩
    · simpa only [equal] using latentPair_edge_of_adjacent first
  have nextHead : forall child, next = .observed child -> headRows graph m path.nodes child = true := by
    intro child equal
    apply List.any_eq_true.mpr
    refine ⟨.latentPair left right, member, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · apply (stepOnPath_eq_true_iff _ _ _).mpr
      exact ⟨before ++ [previous], after, Or.inl (by
        simpa only [List.append_assoc, List.singleton_append, ← equal] using window)⟩
    · simpa only [equal] using latentPair_edge_of_adjacent second
  rcases first.latentPair_children.1 with previousLeft | previousRight
  · rcases second.latentPair_children.1 with nextLeft | nextRight
    · exact False.elim (previousNotNext (previousLeft.trans nextLeft.symm))
    · exact ⟨previousHead left previousLeft, nextHead right nextRight⟩
  · rcases second.latentPair_children.1 with nextLeft | nextRight
    · exact ⟨nextHead left nextLeft, previousHead right previousRight⟩
    · exact False.elim (previousNotNext (previousRight.trans nextRight.symm))

/-- A used original root contributes at both original endpoint heads,
irrespective of which expanded alias occurs on the actual path. -/
theorem pairUsed_children_are_heads {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (root : Fin (pairRootCount graph)) (used : pairUsed graph path.nodes root = true) :
    headRows graph m path.nodes ((pairRoots graph).get root).1 = true ∧
      headRows graph m path.nodes ((pairRoots graph).get root).2 = true := by
  rcases (pairUsed_eq_true_iff graph path.nodes root).mp used with ordered | reversed
  · exact latentPair_children_are_heads path _ _ ordered
  · have heads := latentPair_children_are_heads path _ _ reversed
    exact ⟨heads.2, heads.1⟩

/-- Every incident child of a used original root is a selected head.  This
is proved from the path, rather than assumed to justify the mask guard. -/
theorem pairUsed_incident_head {graph : ObservedGraph S} {m : GraphMutilation S}
    {given : NodeSet S} {source target : Fin S.count}
    (path : ActivePath graph m given (.observed source) (.observed target))
    (root : Fin (pairRootCount graph)) (child : Fin S.count)
    (used : pairUsed graph path.nodes root = true) (incident : pairRootIncident graph root child = true) :
    headRows graph m path.nodes child = true := by
  have heads := pairUsed_children_are_heads path root used
  rcases (pairRootIncident_iff graph root child).mp incident with left | right
  · simpa only [left] using heads.1
  · simpa only [right] using heads.2

end ActivePathInput

end Causality
end Thesis
