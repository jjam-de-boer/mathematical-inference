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
      dsimp only []
      by_cases owner : source = node
      · subst source
        simp only
        rw [HiddenDAGPlacedNoise.encode_of_placed model compatible roots node root placed]
        rfl
      · simp only [if_neg owner]
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

/-- Abstract the placement before inspecting its dependent delivery route.
Keeping that parameter explicit lets the route's source vary together with
its path type; generalizing just an occurrence inside `observedRoots` would
leave an ill-typed dependent match.  Agreement with the actual allocation
still controls every local-noise or shared-source read. -/
private theorem deliveredRoot_expectedValue (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (signals : S.Assignment)
    (roots : model.latent.Assignment) (child : Fin S.count) (root : Fin model.latent.count)
    (incident : model.latent.incident root child = true)
    (placement : HiddenDAGRootPlacement model.latent P root)
    (allocated : model.hiddenDAGRootPlacements compatible root = placement) :
    (let delivery := placement.delivery child incident;
      rootAlongRoute model P (P.hiddenDAG.observedNode child)
        (fun parent _edge => expectedValue model compatible signals roots parent)
        (HiddenDAGPlacedNoise.encode model compatible roots (P.hiddenDAG.observedNode child))
        root delivery.source delivery.route) =
      roots root := by
  cases placement with
  | unused absent =>
      rw [absent child] at incident
      cases incident
  | privateInput ownChild ownIncident onlyChild =>
      have same : child = ownChild := onlyChild child incident
      have placed : (model.hiddenDAGRootPlacements compatible root).source? =
          some (P.hiddenDAG.observedNode child) := by
        rw [allocated]
        change some (P.hiddenDAG.observedNode ownChild) = some (P.hiddenDAG.observedNode child)
        rw [same]
      change (HiddenDAGPlacedNoise.encode model compatible roots
        (P.hiddenDAG.observedNode child) root).getD (defaultRoots model root) = roots root
      rw [HiddenDAGPlacedNoise.encode_of_placed model compatible roots _ root placed]
      rfl
  | sharedInput source hidden routes =>
      have placed : (model.hiddenDAGRootPlacements compatible root).source? = some source := by
        rw [allocated]
        rfl
      change rootAlong model P (P.hiddenDAG.observedNode child)
        (fun parent _edge => expectedValue model compatible signals roots parent)
        root (routes child incident) = roots root
      exact rootAlong_expectedValue model compatible signals roots root source
        (P.hiddenDAG.observedNode child) placed hidden (routes child incident)

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
  exact deliveredRoot_expectedValue model compatible signals roots child root incident
    (model.hiddenDAGRootPlacements compatible root) rfl

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

/-- The complete hidden-node equation reproduces the explicit payload on
the supplied assignment and encoded noise.  This combines both coordinate
families without identifying independent root inputs with observed signals. -/
theorem mechanism_expectedValue_hidden (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (signals : S.Assignment)
    (roots : model.latent.Assignment) (node : Fin P.hiddenDAG.count)
    (missing : P.hiddenDAG.observedIndex node = none) :
    mechanism model compatible node
      (fun parent _edge => expectedValue model compatible signals roots parent)
      (HiddenDAGPlacedNoise.encode model compatible roots node) =
      expectedValue model compatible signals roots node := by
  rw [expectedValue_hidden model compatible signals roots node missing]
  unfold mechanism
  split
  · apply congrArg (nodeValue_of_none model node missing).mpr
    exact Prod.ext (hiddenSignals_expectedValue model compatible signals roots node)
      (hiddenRoots_expectedValue model compatible signals roots node)
  · rename_i index found
    rw [missing] at found
    cases found

/-- At an observed node the complete constructed equation is the original
equation on the reconstructed parents and root values, converted through
the explicit unchanged observed presentation. -/
theorem mechanism_expectedValue_observed (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) (signals : S.Assignment)
    (roots : model.latent.Assignment) (child : Fin S.count) :
    mechanism model compatible (P.hiddenDAG.observedNode child)
      (fun parent _edge => expectedValue model compatible signals roots parent)
      (HiddenDAGPlacedNoise.encode model compatible roots (P.hiddenDAG.observedNode child)) =
      (observedEquivalence model P child).backward
        (model.mechanism child (fun parent _edge => signals parent) (fun root _incident => roots root)) := by
  unfold mechanism
  split
  · rename_i missing
    have found := P.hiddenDAG.observedIndex_observed child
    rw [missing] at found
    cases found
  · rename_i index found
    have same : index = child := Option.some.inj
      (found.symm.trans (P.hiddenDAG.observedIndex_observed child))
    subst index
    exact congrArg (observedEquivalence model P child).backward
      (observedMechanism_expectedValue model compatible signals roots child)

end HiddenDAGRelay
end Causality
end Thesis
