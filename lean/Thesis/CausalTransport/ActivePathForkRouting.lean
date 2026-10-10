import Thesis.CausalTransport.HedgeChannelEnvironmentAbsorption
import Thesis.CausalTransport.HedgeChannelPathInputs
import Thesis.CausalTransport.ActivePathBoundary

namespace Thesis
namespace Causality

open PathSpecification Probability HedgeChannelInstallation HedgeChannelEnvironmentInstallation

variable {S : ObservedSignature.{0}}

/-!
# Route an omitted observed path fork through an actual outgoing path head

An observed path vertex without an incoming path arrow is not an installed
head.  On a nonsingleton path it nevertheless has a real neighbour, and every
such adjacent arrow must point outward.  The neighbour is consequently an
observed receiving head.  A finite scan chooses one actual outgoing head;
no neighbour or edge is selected from propositional existence.

The restricted policy below permits any selected subset of these omitted
vertices.  It stops at all original heads, has only genuine declared arrows,
and has no sink outside those heads.  Absorbing its selected rows therefore
preserves the original path-head phase at every original cube assignment.

Its crucial additional property is local: at the chosen receiver, the new
parent mask cancels the already installed path input.  Other original path
inputs remain present.  This accounts for the nonzero fork read instead of
assuming it away, and supplies a parity-aware exit when an all-Small approach
first contacts an omitted normalized-path fork.  Constructing the complete
all-Small policy and a universally supported odd direction remains separate.
-/

namespace PathSpecification.ActivePath

open ActivePathInput

-- Membership in a nonsingleton actual list supplies a neighbour in Prop.
-- The singleton contradiction is explicitly eliminated from `False`:
-- arithmetic automation at an existential target can otherwise introduce
-- classical contradiction even though the numerical inconsistency is finite.
private theorem neighbor_of_mem : forall nodes : List (SeparationNode S), forall node,
    2 ≤ nodes.length -> node ∈ nodes -> Exists fun neighbor => stepOnPath node neighbor nodes = true
  | [], _, _, visited => by cases visited
  | [_head], _, length, _ =>
      False.elim ((by decide : ¬ 2 ≤ 1) length)
  | head :: next :: rest, node, _length, visited => by
      rcases List.mem_cons.mp visited with first | later
      · subst node
        exact ⟨next, (stepOnPath_eq_true_iff head next _).mpr ⟨[], rest, Or.inl rfl⟩⟩
      · rcases List.mem_cons.mp later with second | remaining
        · subst node
          exact ⟨head, (stepOnPath_eq_true_iff next head _).mpr ⟨[], rest, Or.inr rfl⟩⟩
        · cases rest with
          | nil => cases remaining
          | cons third tail =>
              have length : 2 ≤ (next :: third :: tail).length := by simp only [List.length_cons]; omega
              rcases neighbor_of_mem (next :: third :: tail) node length
                (List.mem_cons.mpr (Or.inr remaining)) with ⟨neighbor, found⟩
              refine ⟨neighbor, ?_⟩
              rw [stepOnPath, found]
              exact Bool.or_true _

variable {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
    {source target : Fin S.count} (path : ActivePath graph m given (.observed source) (.observed target))

/-- Actual observed path vertices omitted by the incoming-head selection.
This includes an outgoing endpoint if selected by a later domain mask; no
endpoint is silently reclassified as an internal fork or collider. -/
def forkNodes : NodeSet S := fun node =>
  path.nodes.any (fun entry => SeparationNode.beq entry (.observed node)) && !(headRows graph m path.nodes node)

/-- The fork mask is precisely actual observed membership without a head.
The description is propositional; the mask itself is the executable scan. -/
theorem forkNodes_eq_true_iff (node : Fin S.count) :
    path.forkNodes node = true ↔ .observed node ∈ path.nodes ∧ headRows graph m path.nodes node = false := by
  unfold forkNodes
  simp only [Bool.and_eq_true_iff, any_beq_eq_true_iff, Bool.not_eq_true']

private theorem outgoing_head_exists (distinct : source ≠ target) (parent : Fin S.count)
    (selected : path.forkNodes parent = true) :
    Exists fun child : Fin S.count => incomingEdge graph m path.nodes (.observed parent) child = true := by
  have parts := (path.forkNodes_eq_true_iff parent).mp selected
  have length : 2 ≤ path.nodes.length := by
    cases shape : path.nodes with
    | nil => have impossible := path.starts; rw [shape] at impossible; cases impossible
    | cons head tail =>
        cases tail with
        | nil =>
            have starts := path.starts
            have finishes := path.finishes
            rw [shape, List.head?_cons] at starts
            rw [shape, List.getLast?_singleton] at finishes
            exact False.elim (distinct (SeparationNode.observed.inj (Option.some.inj (starts.symm.trans finishes))))
        | cons next rest => simp only [List.length_cons]; omega
  rcases neighbor_of_mem path.nodes (.observed parent) length parts.1 with ⟨neighbor, step⟩
  have adjacent : Adjacent graph m (.observed parent) neighbor := by
    rcases (stepOnPath_eq_true_iff _ _ _).mp step with ⟨before, after, forward | backward⟩
    · exact Consecutive.pair_of_append before after _ _ (forward ▸ path.adjacent)
    · exact (Consecutive.pair_of_append before after _ _ (backward ▸ path.adjacent)).symm
  have outgoing : graph.expandedMutilatedEdge m (.observed parent) neighbor = true := by
    rcases adjacent with outward | inward
    · exact outward
    · have reverseStep : stepOnPath neighbor (.observed parent) path.nodes = true := by
        rw [stepOnPath_symm]
        exact step
      have head := incomingEdge_head (Bool.and_eq_true_iff.mpr ⟨reverseStep, inward⟩)
      rw [parts.2] at head
      cases head
  cases neighbor with
  | latentPair left right => cases outgoing
  | observed child => exact ⟨child, Bool.and_eq_true_iff.mpr ⟨step, outgoing⟩⟩

private theorem outgoing_scan (distinct : source ≠ target) (parent : Fin S.count)
    (selected : path.forkNodes parent = true) :
    (NodeSet.enumerated S).any (fun child => incomingEdge graph m path.nodes (.observed parent) child) = true := by
  rcases path.outgoing_head_exists distinct parent selected with ⟨child, edge⟩
  exact List.any_eq_true.mpr ⟨child, NodeSet.mem_enumerated S child, edge⟩

/-- One executable outgoing path-head choice per actual omitted vertex.
Off-mask vertices keep `none`; the supporting existence proof is consumed
only to certify success of this finite data scan. -/
def forkSuccessor (distinct : source ≠ target) : ForestChild S := fun parent =>
  if selected : path.forkNodes parent = true then
    some (listFirstAny (NodeSet.enumerated S) (fun child => incomingEdge graph m path.nodes (.observed parent) child)
      (path.outgoing_scan distinct parent selected))
  else none

/-- Every returned successor is a genuinely installed original path
input, so its child is an actual head and its declared arrow is available. -/
theorem forkSuccessor_edge (distinct : source ≠ target) {parent child : Fin S.count}
    (edge : path.forkSuccessor distinct parent = some child) :
    path.forkNodes parent = true ∧ incomingEdge graph m path.nodes (.observed parent) child = true := by
  by_cases selected : path.forkNodes parent = true
  · have same : listFirstAny (NodeSet.enumerated S)
        (fun child => incomingEdge graph m path.nodes (.observed parent) child)
        (path.outgoing_scan distinct parent selected) = child := by
      simpa only [forkSuccessor, dif_pos selected, Option.some.injEq] using edge
    exact ⟨selected, same ▸ listFirstAny_pred (NodeSet.enumerated S) _ (path.outgoing_scan distinct parent selected)⟩
  · simp only [forkSuccessor, dif_neg selected] at edge
    cases edge

/-- Every selected omitted vertex really gets an outgoing head. -/
theorem forkSuccessor_isSome (distinct : source ≠ target) (parent : Fin S.count)
    (selected : path.forkNodes parent = true) : (path.forkSuccessor distinct parent).isSome = true := by
  simp only [forkSuccessor, dif_pos selected, Option.isSome_some]

/-- A displayed successful finite scan computes the actual exit.  Clients
can use a proved path window in the nondependent `find?` expression instead
of reducing the normalization search or rewriting through its scan proof. -/
theorem forkSuccessor_of_find (distinct : source ≠ target) {parent child : Fin S.count}
    (selected : path.forkNodes parent = true)
    (found : (NodeSet.enumerated S).find?
      (fun next => incomingEdge graph m path.nodes (.observed parent) next) = some child) :
    path.forkSuccessor distinct parent = some child := by
  unfold forkSuccessor
  rw [dif_pos selected]
  apply congrArg some
  unfold listFirstAny
  split
  · next next scan => exact Option.some.inj (scan.symm.trans found)
  · next empty => rw [found] at empty; cases empty

/-- Retain only the omitted vertices selected by an arbitrary actual
caller mask.  Intersections cannot introduce a new nonpath transmitter. -/
def forkRoutingNodes (selected : NodeSet S) : NodeSet S := NodeSet.inter selected path.forkNodes

/-- Keep one outgoing map at each selected fork; original heads are
receivers and are never resumed by this routing layer. -/
def forkRoutingSuccessor (distinct : source ≠ target) (selected : NodeSet S) : ForestChild S :=
  restrictChild (path.forkRoutingNodes selected) (path.forkSuccessor distinct)

/-- Actual heads cannot be selected fork transmitters. -/
theorem forkRoutingSuccessor_stops_heads (distinct : source ≠ target) (selected : NodeSet S) (child : Fin S.count)
    (head : headRows graph m path.nodes child = true) : path.forkRoutingSuccessor distinct selected child = none := by
  have absent : path.forkRoutingNodes selected child = false := by
    simp only [forkRoutingNodes, NodeSet.inter, forkNodes, head, Bool.not_true, Bool.and_false]
  exact restrictChild_of_false absent

/-- The common policy is well formed on the heads plus selected omitted
rows.  Its destinations are original heads, not guessed continuation vertices. -/
theorem forkRoutingSuccessor_wellFormed (distinct : source ≠ target) (selected : NodeSet S) :
    childWellFormedBool (NodeSet.union (headRows graph m path.nodes) (path.forkRoutingNodes selected))
      (path.forkRoutingSuccessor distinct selected) = true := by
  apply List.all_eq_true.mpr
  intro parent _member
  cases retained : path.forkRoutingNodes selected parent with
  | false =>
      cases NodeSet.union (headRows graph m path.nodes) (path.forkRoutingNodes selected) parent <;>
        simp only [forkRoutingSuccessor, restrictChild, retained, Bool.false_eq_true, if_false]
  | true =>
      cases next : path.forkSuccessor distinct parent with
      | none =>
          have parentIn := NodeSet.subset_union_right (headRows graph m path.nodes) _ parent retained
          simp only [forkRoutingSuccessor, restrictChild, retained, if_true, next, parentIn]
      | some child =>
          have actual := (path.forkSuccessor_edge distinct next).2
          have parentIn := NodeSet.subset_union_right (headRows graph m path.nodes) _ parent retained
          have childIn := NodeSet.subset_union_left _ (path.forkRoutingNodes selected) child (incomingEdge_head actual)
          have declared : S.directed parent child = true :=
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp actual).2).1).1
          simp only [forkRoutingSuccessor, restrictChild, retained, if_true, next, parentIn, childIn, declared, Bool.and_self]

/-- A sink of the complete selected routing domain is an original head.
No sink-coverage or readiness premise is supplied with the selected mask. -/
theorem forkRoutingSinks_subset_heads (distinct : source ≠ target) (selected : NodeSet S) :
    NodeSet.Subset (keptSinks (NodeSet.union (headRows graph m path.nodes) (path.forkRoutingNodes selected))
      (path.forkRoutingSuccessor distinct selected)) (headRows graph m path.nodes) := by
  intro node sink
  have parts := (keptSinks_iff _ _ node).mp sink
  rcases Bool.or_eq_true_iff.mp parts.1 with head | fork
  · exact head
  · have actualFork := (Bool.and_eq_true_iff.mp fork).2
    have present := path.forkSuccessor_isSome distinct node actualFork
    have stopped : path.forkSuccessor distinct node = none := (restrictChild_of_true fork).symm.trans parts.2
    rw [stopped] at present
    cases present

/-- At a returned receiver the fork input is already present in the
original signal.  XOR absorption cancels exactly that duplicate parent read,
not the receiving mechanism's own bit or either original reserved input. -/
theorem forkRouting_cancels_chosen_input (distinct : source ≠ target) (selected : NodeSet S)
    {parent child : Fin S.count} (edge : path.forkRoutingSuccessor distinct selected parent = some child) :
    ((LinearSignal.ofActivePath path).absorbSuccessor (headRows graph m path.nodes)
      (path.forkRoutingSuccessor distinct selected)).parentMask child parent = false := by
  have original : path.forkSuccessor distinct parent = some child := by
    cases retained : path.forkRoutingNodes selected parent with
    | false => simp only [forkRoutingSuccessor, restrictChild, retained, Bool.false_eq_true, if_false] at edge; cases edge
    | true => exact (restrictChild_of_true retained).symm.trans edge
  have input := (path.forkSuccessor_edge distinct original).2
  have head := incomingEdge_head input
  simp only [LinearSignal.absorbSuccessor, LinearSignal.ofActivePath, head, if_true, input, edge, decide_true, Bool.xor_self]

/-- Conservation remains exact for every chosen subset of actual forks.
The independent original root coordinates and the original path character
are retained; this is not yet a supported-direction parity theorem. -/
theorem forkRouting_preserves_phase (distinct : source ≠ target) (selected : NodeSet S) (point : Cube graph) :
    (((LinearSignal.ofActivePath path).absorbSuccessor (headRows graph m path.nodes)
      (path.forkRoutingSuccessor distinct selected)).forestPhase
        (NodeSet.union (headRows graph m path.nodes) (path.forkRoutingNodes selected))).value point =
      ((LinearSignal.ofActivePath path).forestPhase (headRows graph m path.nodes)).value point := by
  have enlarged : NodeSet.union (headRows graph m path.nodes)
      (NodeSet.union (headRows graph m path.nodes) (path.forkRoutingNodes selected)) =
      NodeSet.union (headRows graph m path.nodes) (path.forkRoutingNodes selected) := by
    funext node
    change (headRows graph m path.nodes node || (headRows graph m path.nodes node || path.forkRoutingNodes selected node)) =
      (headRows graph m path.nodes node || path.forkRoutingNodes selected node)
    cases headRows graph m path.nodes node <;> cases path.forkRoutingNodes selected node <;> rfl
  rw [← enlarged]
  exact LinearSignal.absorbSuccessor_forestPhase _ _ _ _
    (path.forkRoutingSuccessor_wellFormed distinct selected)
    (path.forkRoutingSuccessor_stops_heads distinct selected)
    (path.forkRoutingSinks_subset_heads distinct selected) point

end PathSpecification.ActivePath

end Causality
end Thesis
