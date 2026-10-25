import Thesis.Causality.ComponentConnectivity

namespace Thesis
namespace Causality

/-!
# C forests from finite component and child-map witnesses

A finite bidirected component and a checked kept-child map determine a
`CForest` whose roots are exactly the kept sinks. These constructors retain
the supplied graph and vertices; they do not choose extra directed edges or
ask for a particular identification program to have failed.

The Boolean connectedness constructor reflects its explicit finite test into
the inductive component proposition. The seed constructor uses the existing
induced-child map, which drops extra edges rather than assuming a functional
out-degree condition on the original graph.

This graph-only module supplies current failure extraction without importing
an identification program or assuming that a semantic countermodel exists.
-/

/--
A bidirected component with a well-formed kept-child map is a `CForest`
on its kept-edge sinks.
-/
theorem cForest_of_component_child
    (G : ObservedGraph S) (nodes : NodeSet S) (child : ForestChild S)
    (hcomp : BidirectedComponent G nodes)
    (hwell : childWellFormedBool nodes child = true) :
    CForest G nodes (keptSinks nodes child) child where
  component := hcomp
  child_off_set := fun _ hp => childWellFormed_off nodes child hwell hp
  child_edge := fun _ _ hc => childWellFormed_edge nodes child hwell hc
  roots_exact := fun i => keptSinks_iff nodes child i

/--
A Boolean-connected node set with a well-formed kept-child map is a
`CForest` on its kept-edge sinks.
-/
theorem cForest_of_child
    (G : ObservedGraph S) (nodes : NodeSet S) (child : ForestChild S)
    (hsingle : G.isSingleCComponent nodes = true)
    (hwell : childWellFormedBool nodes child = true) :
    CForest G nodes (keptSinks nodes child) child := by
  rcases isSingleCComponent_spec G nodes hsingle with ⟨root, hroot, hEq⟩
  exact cForest_of_component_child G nodes child
    (by
      rw [hEq]
      exact cComponentOf_is_component G nodes hroot)
    hwell

/--
The executable c-component of a seed, with its induced child map, is a
`CForest`.  Extra induced directed edges are dropped by `inducedChild`.
-/
theorem cForest_of_thinned_component
    (G : ObservedGraph S) (nodes : NodeSet S) {seed : Fin S.count}
    (hseed : nodes seed = true) :
    CForest G (G.cComponentOf nodes seed)
      (keptSinks (G.cComponentOf nodes seed)
        (inducedChild (G.cComponentOf nodes seed)))
      (inducedChild (G.cComponentOf nodes seed)) :=
  cForest_of_component_child G (G.cComponentOf nodes seed)
    (inducedChild (G.cComponentOf nodes seed))
    (cComponentOf_is_component G nodes hseed)
    (inducedChild_wellFormed _)

end Causality
end Thesis
