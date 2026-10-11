import Thesis.Causality.HiddenPathSearch

namespace Thesis
namespace Causality

/-!
# Executable common-cause data for a projected bidirected edge

Countermodel lifting needs an actual hidden source and actual relay paths,
not just an existential projection statement in `Prop`.  Search the supplied
finite hidden graph for the first source with both computed incidences.
Successful search retains its hidden-node proof and both previously searched
hidden-internal paths.  The completeness proof shows that the existing
projection specification makes this computed option available; it does not
choose data from the existential witness.

Distinct endpoints are required, exactly as in `projectedBidirected`.  A
common ancestor with more observed descendants is not split or duplicated:
later independent channels can be allocated at that one real hidden node.
This module supplies the graph data for that construction, not a distribution
preservation theorem or a completeness assumption.
-/

namespace FiniteHiddenDAG

/-- One actual hidden source and its two nonempty hidden-internal routes.
The endpoint distinction excludes reflexive projected bidirected edges. -/
structure HiddenCommonCauseData (H : FiniteHiddenDAG S) (left right : Fin S.count) where
  different : left ≠ right
  source : Fin H.count
  hidden : H.hidden source = true
  leftPath : H.HiddenInternalPathData source (H.observedNode left)
  rightPath : H.HiddenInternalPathData source (H.observedNode right)

/-- Retained data satisfies the original common-cause specification. -/
def HiddenCommonCauseData.toSpecification
    {H : FiniteHiddenDAG S} {left right : Fin S.count}
    (cause : HiddenCommonCauseData H left right) : H.projectedBidirected left right :=
  ⟨cause.different, cause.source, cause.hidden,
    cause.leftPath.toSpecification, cause.rightPath.toSpecification⟩

/-- Scan the graph's actual finite node order, using the exact path-support
tags rather than a separately supplied ancestry relation.  Both paths are
read from their computed options, not selected from existence propositions. -/
def hiddenCommonCause? (H : FiniteHiddenDAG S) (left right : Fin S.count) :
    Option (HiddenCommonCauseData H left right) :=
  if different : left ≠ right then
    match found : (List.finRange H.count).find? (fun source =>
        H.hiddenInputIncident source left && H.hiddenInputIncident source right) with
    | none => none
    | some source =>
        let selected : (H.hiddenInputIncident source left && H.hiddenInputIncident source right) = true :=
          List.find?_some (p := fun candidate =>
            H.hiddenInputIncident candidate left && H.hiddenInputIncident candidate right) found
        let incidences := Bool.and_eq_true_iff.mp selected
        let leftIncident := (H.hiddenInputIncident_iff source left).mp incidences.1
        let rightIncident := (H.hiddenInputIncident_iff source right).mp incidences.2
        some {
          different := different
          source := source
          hidden := leftIncident.1
          leftPath := leftIncident.2.toData
          rightPath := rightIncident.2.toData
        }
  else none

/-- Every specified projected bidirected edge has a successful computed
common-cause search.  The existential source is used only to contradict a
failed finite scan; the returned data remains determined by the scan itself. -/
theorem hiddenCommonCause?_complete (H : FiniteHiddenDAG S)
    {left right : Fin S.count} (edge : H.projectedBidirected left right) :
    (H.hiddenCommonCause? left right).isSome = true := by
  rcases edge with ⟨different, source, hidden, leftPath, rightPath⟩
  have selected : (H.hiddenInputIncident source left && H.hiddenInputIncident source right) = true :=
    Bool.and_eq_true_iff.mpr
      ⟨(H.hiddenInputIncident_iff source left).mpr ⟨hidden, leftPath⟩,
        (H.hiddenInputIncident_iff source right).mpr ⟨hidden, rightPath⟩⟩
  unfold hiddenCommonCause?
  rw [dif_pos different]
  split
  · rename_i missing
    exact False.elim ((List.find?_eq_none.mp missing) source (List.mem_finRange source) selected)
  · rfl

/-- A successful search is sound, including hidden-interior and endpoint
conventions; the actual retained paths prove the specification directly. -/
theorem hiddenCommonCause?_sound (H : FiniteHiddenDAG S)
    {left right : Fin S.count}
    (found : (H.hiddenCommonCause? left right).isSome = true) :
    H.projectedBidirected left right :=
  ((H.hiddenCommonCause? left right).get found).toSpecification

theorem hiddenCommonCause?_iff (H : FiniteHiddenDAG S) (left right : Fin S.count) :
    (H.hiddenCommonCause? left right).isSome = true <-> H.projectedBidirected left right :=
  ⟨H.hiddenCommonCause?_sound, H.hiddenCommonCause?_complete⟩

/-- Read the deterministically computed cause and relay data.  The
specification proof supplies only the successful option tag. -/
def projectedBidirected.toData {H : FiniteHiddenDAG S} {left right : Fin S.count}
    (edge : H.projectedBidirected left right) : HiddenCommonCauseData H left right :=
  (H.hiddenCommonCause? left right).get (H.hiddenCommonCause?_complete edge)

end FiniteHiddenDAG
end Causality
end Thesis
