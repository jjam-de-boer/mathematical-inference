import Thesis.CausalTransport.HiddenDAGRelayAssignment

namespace Thesis
namespace Causality

/-!
# Local equations for the reverse hidden-DAG construction

The relay assignment supplies arbitrary observed signals and original root
values.  Here the actual constructed mechanisms are evaluated on that
assignment and the explicit allocated-noise encoding.  Every hidden signal,
hidden root coordinate, declared observed parent and declared observed input
is proved to have the intended value.

These local equalities use the all-path readback lemmas, not observational
positivity, factor marginals or a semantic transfer assumption.  Private
inputs are read at their own observed recipient; shared inputs are read from
the actual hidden source; unused roots cannot occur as declared inputs.

The observed mechanism is deliberately not equated to an arbitrary supplied
signal.  It is equated to the original equation applied to the supplied
parent signals and root values.  The later unit-preservation proof must use
the original *intervened* evaluation to satisfy those observed equations.
-/

namespace HiddenDAGRelay

variable {S : ObservedSignature.{0}} {P : FiniteLatentProjection S}

/-- All hidden observed-signal coordinates agree with the explicit relay
assignment, whether the finite path search succeeds or correctly finds no
route.  Required routes cannot take the off-route default branch. -/
theorem hiddenSignals_expectedValue (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (signals : S.Assignment)
    (roots : model.latent.Assignment) (node : Fin P.hiddenDAG.count) :
    hiddenSignals model P node (fun parent _edge => expectedValue model compatible signals roots parent) =
      expectedSignals P signals node := by
  funext index
  unfold hiddenSignals expectedSignals
  cases found : P.hiddenDAG.hiddenInternalPath? (P.hiddenDAG.observedNode index) node with
  | none => rfl
  | some path => exact signalAlong_expectedValue model compatible signals roots index node path

/-- Hidden root channels agree with the explicit assignment.  At the owner
the encoded local noise contains the original value; elsewhere a genuine
hidden route forwards that value.  Other slots retain the same total default. -/
theorem hiddenRoots_expectedValue (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (signals : S.Assignment)
    (roots : model.latent.Assignment) (node : Fin P.hiddenDAG.count) :
    hiddenRoots model compatible node
      (fun parent _edge => expectedValue model compatible signals roots parent)
      (HiddenDAGPlacedNoise.encode model compatible roots node) =
      expectedRoots model compatible roots node := by
  funext root
  unfold hiddenRoots expectedRoots
  cases placed : (model.hiddenDAGRootPlacements compatible root).source? with
  | none => rfl
  | some source =>
      by_cases owner : source = node
      · subst source
        rw [if_pos rfl, HiddenDAGPlacedNoise.encode_of_placed model compatible roots node root placed]
        rfl
      · rw [if_neg owner]
        cases hidden : P.hiddenDAG.hidden source with
        | false => rfl
        | true =>
            cases found : P.hiddenDAG.hiddenInternalPath? source node with
            | none => rfl
            | some path =>
                exact rootAlong_expectedValue model compatible signals roots root source node
                  placed hidden path

/-- Every parent input of the original observed equation receives exactly
that parent's supplied observed signal, through the original DAG's actual
computed projected-edge route. -/
theorem observedParents_expectedValue (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (signals : S.Assignment)
    (roots : model.latent.Assignment) (child : Fin S.count) :
    observedParents model P child
      (fun parent _edge => expectedValue model compatible signals roots parent) =
      (fun parent _edge => signals parent) := by
  funext parent edge
  exact signalAlong_expectedValue model compatible signals roots parent
    (P.hiddenDAG.observedNode child) (P.directedPathData parent child edge)

/-- Every declared root input of an observed equation receives its original
coordinate.  The proof inspects the constructed placement data, so a private
input uses its own local channel and a shared input has a hidden source.
No arbitrary route record is assumed to have a hidden source. -/
theorem observedRoots_expectedValue (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (signals : S.Assignment)
    (roots : model.latent.Assignment) (child : Fin S.count) :
    observedRoots model compatible child
      (fun parent _edge => expectedValue model compatible signals roots parent)
      (HiddenDAGPlacedNoise.encode model compatible roots (P.hiddenDAG.observedNode child)) =
      (fun root _incident => roots root) := by
  funext root incident
  unfold observedRoots
  cases placement : model.hiddenDAGRootPlacements compatible root with
  | unused absent =>
      rw [absent child] at incident
      cases incident
  | privateInput ownChild ownIncident onlyChild =>
      have same : child = ownChild := onlyChild child incident
      have placed : (model.hiddenDAGRootPlacements compatible root).source? =
          some (P.hiddenDAG.observedNode child) := by
        rw [placement]
        change some (P.hiddenDAG.observedNode ownChild) = some (P.hiddenDAG.observedNode child)
        rw [same]
      change (HiddenDAGPlacedNoise.encode model compatible roots
        (P.hiddenDAG.observedNode child) root).getD (defaultRoots model root) = roots root
      rw [HiddenDAGPlacedNoise.encode_of_placed model compatible roots _ root placed]
      rfl
  | sharedInput source hidden routes =>
      have placed : (model.hiddenDAGRootPlacements compatible root).source? = some source := by
        rw [placement]
        rfl
      change rootAlong model P (P.hiddenDAG.observedNode child)
        (fun parent _edge => expectedValue model compatible signals roots parent)
        root (routes child incident) = roots root
      exact rootAlong_expectedValue model compatible signals roots root source
        (P.hiddenDAG.observedNode child) placed hidden (routes child incident)

/-- Reconstructed observed inputs reproduce the original structural
equation on the supplied parent signals and original root values.  Forced
values are handled separately by the evaluator's intervention match. -/
theorem observedMechanism_expectedValue (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (signals : S.Assignment)
    (roots : model.latent.Assignment) (child : Fin S.count) :
    observedMechanism model compatible child
      (fun parent _edge => expectedValue model compatible signals roots parent)
      (HiddenDAGPlacedNoise.encode model compatible roots (P.hiddenDAG.observedNode child)) =
      model.mechanism child (fun parent _edge => signals parent) (fun root _incident => roots root) := by
  unfold observedMechanism
  rw [observedParents_expectedValue, observedRoots_expectedValue]

end HiddenDAGRelay
end Causality
end Thesis
