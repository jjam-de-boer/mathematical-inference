import Thesis.CausalTransport.ActivePathForkOrientation
import Thesis.CausalTransport.ActivePathHeadInputs

namespace Thesis
namespace Causality

open PathSpecification

universe u v

/-!
# Literal bridges between successive heads in the original active-path order

The incidence argument must walk the actual normalized list, not an unordered
set of selected rows.  We project that list to its incoming observed heads.
An omitted observed vertex is a genuine outgoing fork, while a latent vertex
has only observed receiving neighbours.  Thus two omitted vertices cannot be
consecutive: successive heads are either adjacent in the expanded list or
separated by precisely one actual latent root or one omitted observed fork.

The bridge description retains the literal prefix/window/suffix decomposition
of the original list.  It does not contract a latent input into an observed
arrow, pick a new reserved root, or assert that an absorbed fork still connects
both sides.  The conditional incidence layer will separately interpret each
window using its actual installed columns and retained-fork contact alternative.

All projection data are executable finite list operations.  The window and
bridge witnesses below live in Prop only; no data are chosen from existence.
-/

namespace PathSpecification.Consecutive

/-- Project a list whose omissions are isolated.  Two retained neighbours
use their literal pair certificate; a single omitted middle uses its literal
triple certificate.  The proof never searches for an unspecified first or
last retained element and needs no decidability of the target relation. -/
theorem filterMap_of_isolated_omissions {α : Type u} {β : Type v} (select : α -> Option β)
    (relation : β -> β -> Prop) : forall nodes : List α,
    (forall before after left right, nodes = before ++ left :: right :: after ->
      select left = none -> select right = none -> False) ->
    (forall before after left right a b, nodes = before ++ left :: right :: after ->
      select left = some a -> select right = some b -> relation a b) ->
    (forall before after left middle right a b,
      nodes = before ++ left :: middle :: right :: after ->
      select left = some a -> select middle = none -> select right = some b -> relation a b) ->
    Consecutive relation (nodes.filterMap select)
  | [], _isolated, _pairs, _triples => True.intro
  | first :: tail, isolated, pairs, triples => by
      have tailProof := filterMap_of_isolated_omissions select relation tail
        (fun before after left right window => isolated (first :: before) after left right (congrArg (List.cons first) window))
        (fun before after left right a b window => pairs (first :: before) after left right a b (congrArg (List.cons first) window))
        (fun before after left middle right a b window =>
          triples (first :: before) after left middle right a b (congrArg (List.cons first) window))
      cases firstSelected : select first with
      | none => simpa only [List.filterMap_cons_none firstSelected] using tailProof
      | some a =>
          cases tail with
          | nil => simp only [List.filterMap_cons_some firstSelected, List.filterMap_nil, Consecutive]
          | cons second rest =>
              cases secondSelected : select second with
              | some b =>
                  rw [List.filterMap_cons_some firstSelected, List.filterMap_cons_some secondSelected]
                  exact ⟨pairs [] rest first second a b rfl firstSelected secondSelected,
                    by simpa only [List.filterMap_cons_some secondSelected] using tailProof⟩
              | none =>
                  cases rest with
                  | nil => simp only [List.filterMap_cons_some firstSelected, List.filterMap_cons_none secondSelected,
                      List.filterMap_nil, Consecutive]
                  | cons third after =>
                      cases thirdSelected : select third with
                      | none => exact False.elim (isolated [first] after second third rfl secondSelected thirdSelected)
                      | some b =>
                          rw [List.filterMap_cons_some firstSelected, List.filterMap_cons_none secondSelected,
                            List.filterMap_cons_some thirdSelected]
                          exact ⟨triples [] after first second third a b rfl firstSelected secondSelected thirdSelected,
                            by simpa only [List.filterMap_cons_none secondSelected,
                              List.filterMap_cons_some thirdSelected] using tailProof⟩

end PathSpecification.Consecutive

namespace ActivePathInput

variable {S : ObservedSignature.{0}}

/-- Keep one observed row exactly when it is an actual incoming head of
the supplied original list.  Latent aliases and omitted observed forks have
no own installed head row; neither is replaced by a synthetic vertex. -/
def headProjection (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) : SeparationNode S -> Option (Fin S.count)
  | .observed row => if headRows graph m nodes row then some row else none
  | .latentPair _ _ => none

/-- A returned row is literally that observed vertex and a genuine head.
This characterization supplies both identities when a projected bridge is
interpreted in the original expanded graph. -/
theorem headProjection_eq_some_iff (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (entry : SeparationNode S) (row : Fin S.count) :
    headProjection graph m nodes entry = some row ↔
      entry = .observed row ∧ headRows graph m nodes row = true := by
  cases entry with
  | latentPair _ _ =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨impossible, _head⟩; cases impossible
  | observed node =>
      cases selected : headRows graph m nodes node with
      | false =>
          simp only [headProjection, selected, Bool.false_eq_true, if_false]
          constructor
          · intro impossible; cases impossible
          · rintro ⟨same, head⟩
            cases same
            exact False.elim (Bool.false_ne_true (selected.symm.trans head))
      | true =>
          simp only [headProjection, selected, if_true]
          constructor
          · intro same
            have equal : node = row := Option.some.inj same
            subst node
            exact ⟨rfl, selected⟩
          · rintro ⟨same, _head⟩
            cases same
            rfl

/-- Original-list order of the incoming observed heads.  The classifier
continues to use the whole original list, not the progressively shorter
suffix which the structural proof happens to inspect. -/
def headNodes (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) : List (Fin S.count) :=
  nodes.filterMap (headProjection graph m nodes)

/-- Exactly the original incoming head rows occur in the projected list.
Actual path membership follows from the incoming-edge classifier itself. -/
theorem mem_headNodes_iff (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (row : Fin S.count) :
    row ∈ headNodes graph m nodes ↔ headRows graph m nodes row = true := by
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with ⟨entry, _visited, projected⟩
    exact ((headProjection_eq_some_iff graph m nodes entry row).mp projected).2
  · intro head
    exact List.mem_filterMap.mpr ⟨.observed row, headRows_member head,
      (headProjection_eq_some_iff graph m nodes _ row).mpr ⟨rfl, head⟩⟩

/-- A projected step retains its actual original window and both genuine
head identities.  The final alternative is an omitted observed fork, not a
promise that the two heads remain connected after absorption. -/
def HeadBridge (graph : ObservedGraph S) (m : GraphMutilation S)
    (nodes : List (SeparationNode S)) (left right : Fin S.count) : Prop :=
  headRows graph m nodes left = true ∧ headRows graph m nodes right = true ∧
    ((Exists fun before => Exists fun after => nodes = before ++ .observed left :: .observed right :: after) ∨
      (Exists fun before => Exists fun after => Exists fun rootLeft => Exists fun rootRight =>
        nodes = before ++ .observed left :: .latentPair rootLeft rootRight :: .observed right :: after) ∨
      (Exists fun before => Exists fun after => Exists fun parent =>
        nodes = before ++ .observed left :: .observed parent :: .observed right :: after ∧
          headRows graph m nodes parent = false))

variable {graph : ObservedGraph S} {m : GraphMutilation S} {given : NodeSet S}
    {source target : Fin S.count}

-- Every arrow of a literal pair selects its observed receiving endpoint.
-- Expanded latent vertices can only be parents, so even a latent/observed
-- pair has a real projected head.  This rules out consecutive omissions.
private theorem pair_has_projected_head
    (path : ActivePath graph m given (.observed source) (.observed target))
    (before after : List (SeparationNode S)) (left right : SeparationNode S)
    (window : path.nodes = before ++ left :: right :: after) :
    (Exists fun row => headProjection graph m path.nodes left = some row) ∨
      (Exists fun row => headProjection graph m path.nodes right = some row) := by
  have adjacent := Consecutive.pair_of_append before after left right (window ▸ path.adjacent)
  have step : stepOnPath left right path.nodes = true :=
    (stepOnPath_eq_true_iff left right path.nodes).mpr ⟨before, after, Or.inl window⟩
  rcases adjacent with forward | backward
  · cases right with
    | latentPair _ _ => cases left <;> cases forward
    | observed row =>
        exact Or.inr ⟨row, (headProjection_eq_some_iff graph m path.nodes _ row).mpr
          ⟨rfl, incomingEdge_head (Bool.and_eq_true_iff.mpr ⟨step, forward⟩)⟩⟩
  · cases left with
    | latentPair _ _ => cases right <;> cases backward
    | observed row =>
        rw [stepOnPath_symm] at step
        exact Or.inl ⟨row, (headProjection_eq_some_iff graph m path.nodes _ row).mpr
          ⟨rfl, incomingEdge_head (Bool.and_eq_true_iff.mpr ⟨step, backward⟩)⟩⟩

/-- Every successive pair of projected heads has precisely one of the
three genuine literal bridge forms.  The isolated-omission argument is
structural in the original list, so no global connectivity or installation
readiness premise is smuggled into this graph-only result. -/
theorem headNodes_consecutive_bridges
    (path : ActivePath graph m given (.observed source) (.observed target)) :
    Consecutive (HeadBridge graph m path.nodes) (headNodes graph m path.nodes) := by
  apply Consecutive.filterMap_of_isolated_omissions
  · intro before after left right window leftNone rightNone
    rcases pair_has_projected_head path before after left right window with ⟨row, selected⟩ | ⟨row, selected⟩
    · rw [leftNone] at selected; cases selected
    · rw [rightNone] at selected; cases selected
  · intro before after left right a b window leftSelected rightSelected
    rcases (headProjection_eq_some_iff graph m path.nodes left a).mp leftSelected with ⟨leftEq, leftHead⟩
    rcases (headProjection_eq_some_iff graph m path.nodes right b).mp rightSelected with ⟨rightEq, rightHead⟩
    exact ⟨leftHead, rightHead, Or.inl ⟨before, after, by simpa only [leftEq, rightEq] using window⟩⟩
  · intro before after left middle right a b window leftSelected middleNone rightSelected
    rcases (headProjection_eq_some_iff graph m path.nodes left a).mp leftSelected with ⟨leftEq, leftHead⟩
    rcases (headProjection_eq_some_iff graph m path.nodes right b).mp rightSelected with ⟨rightEq, rightHead⟩
    refine ⟨leftHead, rightHead, Or.inr ?_⟩
    cases middle with
    | latentPair rootLeft rootRight =>
        exact Or.inl ⟨before, after, rootLeft, rootRight, by simpa only [leftEq, rightEq] using window⟩
    | observed parent =>
        apply Or.inr
        refine ⟨before, after, parent, by simpa only [leftEq, rightEq] using window, ?_⟩
        cases selected : headRows graph m path.nodes parent with
        | false => rfl
        | true =>
            change (if headRows graph m path.nodes parent then some parent else none) = none at middleNone
            rw [selected] at middleNone
            cases middleNone

/-- An incoming observed endpoint is the last head in the original
projected order.  Projection preserves the literal terminal singleton,
including when earlier latent aliases and forks are omitted. -/
theorem headNodes_getLast_of_target_head
    (path : ActivePath graph m given (.observed source) (.observed target))
    (head : headRows graph m path.nodes target = true) :
    (headNodes graph m path.nodes).getLast? = some target := by
  rcases List.getLast?_eq_some_iff.mp path.finishes with ⟨before, window⟩
  have selected := (headProjection_eq_some_iff graph m path.nodes (.observed target) target).mpr ⟨rfl, head⟩
  have projected := congrArg (List.filterMap (headProjection graph m path.nodes)) window
  change headNodes graph m path.nodes = _ at projected
  rw [List.filterMap_append, List.filterMap_cons_some selected, List.filterMap_nil] at projected
  rw [projected, List.getLast?_append, List.getLast?_singleton, Option.some_or]

/-- If the original outcome endpoint points outward, its actual unique
neighbour receives that input and is the last projected head instead.
Reversal identifies the literal final pair, not an arbitrary reachable row.
The endpoint's absent own head follows from rank and its outgoing input. -/
theorem headNodes_getLast_of_target_input
    (path : ActivePath graph m given (.observed source) (.observed target))
    (receiver : Fin S.count)
    (input : incomingEdge graph m path.nodes (.observed target) receiver = true) :
    (headNodes graph m path.nodes).getLast? = some receiver := by
  have receiverHead := incomingEdge_head input
  have targetAbsent : headRows graph m path.nodes target = false := by
    cases head : headRows graph m path.nodes target with
    | false => rfl
    | true => exact False.elim (Bool.false_ne_true ((target_head_parent_absent path head receiver).symm.trans input))
  have reversedInput : incomingEdge graph m path.reverse.nodes (.observed target) receiver = true := by
    change incomingEdge graph m path.nodes.reverse (.observed target) receiver = true
    simpa only [incomingEdge, stepOnPath_reverse] using input
  cases shape : path.reverse.nodes with
  | nil =>
      have impossible := path.reverse.starts
      rw [shape] at impossible
      cases impossible
  | cons first tail =>
      have starts := path.reverse.starts
      rw [shape, List.head?_cons] at starts
      have same := Option.some.inj starts
      subst first
      cases tail with
      | nil =>
          simp only [shape, incomingEdge, stepOnPath, Bool.false_and] at reversedInput
          cases reversedInput
      | cons next rest =>
          have neighbor : .observed receiver = next :=
            (stepOnPath_first_pair (.observed target) next (.observed receiver) rest (shape ▸ path.reverse.simple)).mp
              (by simpa only [shape, stepOnPath_symm] using (Bool.and_eq_true_iff.mp reversedInput).1)
          rw [← neighbor] at shape
          change path.nodes.reverse = .observed target :: .observed receiver :: rest at shape
          have window : path.nodes = rest.reverse ++ [.observed receiver, .observed target] := by
            have back := congrArg List.reverse shape
            simpa only [List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.nil_append,
              List.append_assoc, List.singleton_append] using back
          have receiverSelected := (headProjection_eq_some_iff graph m path.nodes _ receiver).mpr ⟨rfl, receiverHead⟩
          have targetOmitted : headProjection graph m path.nodes (.observed target) = none := by
            simp only [headProjection, targetAbsent, Bool.false_eq_true, if_false]
          have projected := congrArg (List.filterMap (headProjection graph m path.nodes)) window
          change headNodes graph m path.nodes = _ at projected
          rw [List.filterMap_append, List.filterMap_cons_some receiverSelected,
            List.filterMap_cons_none targetOmitted, List.filterMap_nil] at projected
          rw [projected, List.getLast?_append, List.getLast?_singleton, Option.some_or]

end ActivePathInput
end Causality
end Thesis
