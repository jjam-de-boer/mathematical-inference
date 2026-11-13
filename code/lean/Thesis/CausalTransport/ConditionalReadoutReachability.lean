import Thesis.CausalTransport.ConditionalReadoutRoute

namespace Thesis
namespace Causality

/-!
# Constructive directed readout data from an incoming-cut reachability test

Route constructors consume actual vertices and arrows in `Type`.  A graph
availability test must not supply them by eliminating a propositional path
existence theorem.  Here the existing finite successor search constructs the
route directly from the Boolean reachability computation.

Every selected successor comes from the signature's fixed finite enumeration.
Its edge is retained by the incoming cut, so the successor is outside that
cut.  The returned certificate records this for every readout destination.
The source itself is not required to be outside the cut: a length-zero route
has no destination, while a nonempty incoming-cut walk can leave a cut source.
Callers needing a free auxiliary collider parent check it separately.

A hedge caller can cut the union of its action and large forest.  The result
then supplies both action avoidance and outside-forest readiness along an
arbitrary number of directed readouts, without selecting a path by choice.
No causal countermodel or statement of universal active-path coverage is
assumed or proved by this purely graph-data construction.
-/

variable {S : ObservedSignature.{0}}

namespace ConditionalReadout

/-- A genuine directed route whose replaced destinations all avoid the
displayed incoming cut.  The zero-length route is permitted. -/
structure CutRoute (S : ObservedSignature.{0}) (cut : NodeSet S)
    (parent endpoint : Fin S.count) where
  route : Route S parent endpoint
  destinations_free : forall node, node ∈ route.destinations -> cut node = false

/-- Build route data from the executable finite reachability test.  The fuel
decreases at each selected successor.  Equality and successor selection use
only finite Boolean decisions; no existential path is unpacked into data. -/
def CutRoute.ofReachability (cut : NodeSet S) (endpoint : Fin S.count) :
    (fuel : Nat) -> (parent : Fin S.count) ->
      FiniteReachability.within finBeq (NodeSet.enumerated S)
        (mutilatedDirected S cut) fuel parent endpoint = true ->
      CutRoute S cut parent endpoint
  | 0, parent, reachable => by
      have same : parent = endpoint := (finBeq_eq_true_iff parent endpoint).mp (by
        simpa only [FiniteReachability.within, FiniteReachability.closure,
          FiniteReachability.contains, List.any_cons, List.any_nil, Bool.or_false] using reachable)
      subst endpoint
      exact ⟨.refl parent, fun _ listed => by cases listed⟩
  | fuel + 1, parent, reachable => by
      by_cases same : finBeq parent endpoint = true
      · have equal := (finBeq_eq_true_iff parent endpoint).mp same
        subst endpoint
        exact ⟨.refl parent, fun _ listed => by cases listed⟩
      · let candidates := NodeSet.enumerated S
        let continues := fun node => mutilatedDirected S cut parent node &&
          FiniteReachability.within finBeq candidates (mutilatedDirected S cut) fuel node endpoint
        have found : candidates.any continues = true :=
          finiteWithin_successor_any finBeq candidates (mutilatedDirected S cut)
            finBeq_eq_true_iff (NodeSet.mem_enumerated S) reachable (Bool.eq_false_iff.mpr same)
        let next := listFirstAny candidates continues found
        have parts := Bool.and_eq_true_iff.mp (listFirstAny_pred candidates continues found)
        have nextFree := action_false_of_mutilatedDirected cut parts.1
        have edge : S.directed parent next = true := by
          simpa only [mutilatedDirected, nextFree, Bool.false_eq_true, if_false] using parts.1
        let tail := CutRoute.ofReachability cut endpoint fuel next parts.2
        refine ⟨.step edge tail.route, ?_⟩
        intro node listed
        rcases List.mem_cons.mp listed with equal | rest
        · subst node
          exact nextFree
        · exact tail.destinations_free node rest

end ConditionalReadout
end Causality
end Thesis
