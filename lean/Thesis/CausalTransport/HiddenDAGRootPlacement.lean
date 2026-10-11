import Thesis.Causality.HiddenCommonCauseSearch
import Thesis.Causality.Identification

namespace Thesis
namespace Causality

/-!
# Place every canonical input root on the original finite hidden DAG

The forward collapse keeps multi-child roots and preserves their laws.  The
opposite construction has a different task: realize a *canonical* projected-
graph countermodel inside the original hidden DAG.  Every active root of
that countermodel has one or two observed children.  Place a private input
at its child and a two-child input at an actual hidden common ancestor, with
executable hidden-internal paths to every declared child.

This placement is constructed for every root of every canonical latent
extension with the stated projected graph.  It is not an external relay
readiness hypothesis, a fixed pair-root numbering assumption, or a finite
list of specially handled countermodels.  Several distinct roots may be
placed at the same hidden node; they must later occupy *independent channels*
in that node's private-noise vector, not be identified as one random variable.

Unused roots have their own constructor.  No source is invented for them,
so empty observed signatures and empty hidden graphs need no selected default
vertex.  Actual noise grouping, typed hidden-node relay mechanisms and their
probability preservation remain the next model-realization obligations.
-/

variable {S : ObservedSignature} {P : FiniteLatentProjection S}

/-- Complete placement data for one input root.  Shared routes cover every
declared incidence, not merely the two children found by the finite scan. -/
inductive HiddenDAGRootPlacement (latent : LatentExtension S)
    (projection : FiniteLatentProjection S) (root : Fin latent.count) : Type where
  | unused (absent : forall child, latent.incident root child = false)
  | privateInput (child : Fin S.count) (incident : latent.incident root child = true)
      (onlyChild : forall other, latent.incident root other = true -> other = child)
  | sharedInput (source : Fin projection.hiddenDAG.count)
      (hidden : projection.hiddenDAG.hidden source = true)
      (routes : forall child, latent.incident root child = true ->
        projection.hiddenDAG.HiddenInternalPathData source (projection.hiddenDAG.observedNode child))

namespace HiddenDAGRootPlacement

/-- The original full-graph node that receives this root's private random
channel.  An unused root has no observed input delivery obligation. -/
def source? {latent : LatentExtension S} {root : Fin latent.count} :
    HiddenDAGRootPlacement latent P root -> Option (Fin P.hiddenDAG.count)
  | .unused _ => none
  | .privateInput child _ _ => some (P.hiddenDAG.observedNode child)
  | .sharedInput source _ _ => some source

/-- Active input roots always have a genuine source.  This proof is by
the placement data itself, including the impossible unused-input branch. -/
theorem source?_isSome_of_incident {latent : LatentExtension S} {root : Fin latent.count}
    (placement : HiddenDAGRootPlacement latent P root) (child : Fin S.count)
    (incident : latent.incident root child = true) : placement.source?.isSome = true := by
  cases placement with
  | unused absent => rw [absent child] at incident; cases incident
  | privateInput => rfl
  | sharedInput => rfl

end HiddenDAGRootPlacement

/-- A root input is either already at its observed recipient or reaches it
along an actual nonempty hidden-internal path.  Only private inputs use the
zero-length alternative; it is not added to projected bidirected paths. -/
inductive HiddenDAGInputRoute (H : FiniteHiddenDAG S) (source target : Fin H.count) : Type
  | localInput (same : source = target)
  | hiddenRelay (path : H.HiddenInternalPathData source target)

/-- An active input's executable route, together with proof that its source
is the one allocated to that root.  Later mechanisms can inspect the route
without selecting a predecessor from a reachability proposition. -/
structure HiddenDAGRootDelivery {latent : LatentExtension S} {root : Fin latent.count}
    (placement : HiddenDAGRootPlacement latent P root) (child : Fin S.count) where
  source : Fin P.hiddenDAG.count
  placed : placement.source? = some source
  route : HiddenDAGInputRoute P.hiddenDAG source (P.hiddenDAG.observedNode child)

namespace HiddenDAGRootPlacement

/-- Every declared input has delivery data from its root's actual allocated
source.  Both hidden relays and the private local-input case are constructive;
an unused root cannot be passed with an active incidence proof. -/
def delivery {latent : LatentExtension S} {root : Fin latent.count}
    (placement : HiddenDAGRootPlacement latent P root) (child : Fin S.count)
    (incident : latent.incident root child = true) : HiddenDAGRootDelivery placement child := by
  cases placement with
  | unused absent => rw [absent child] at incident; cases incident
  | privateInput ownChild _ownIncident onlyChild =>
      exact {
        source := P.hiddenDAG.observedNode ownChild
        placed := rfl
        route := .localInput (congrArg P.hiddenDAG.observedNode (onlyChild child incident).symm)
      }
  | sharedInput source hidden routes =>
      exact { source := source, placed := rfl, route := .hiddenRelay (routes child incident) }

end HiddenDAGRootPlacement

namespace LatentExtension

/-- A supplied common root with distinct children produces the actual
Boolean projected edge.  This is an intrinsic incidence fact, independent
of any probability model or hidden-DAG projection theorem. -/
theorem projectedBidirected_of_incident (latent : LatentExtension S)
    (root : Fin latent.count) (left right : Fin S.count) (different : left ≠ right)
    (leftIncident : latent.incident root left = true)
    (rightIncident : latent.incident root right = true) :
    latent.projectedBidirected left right = true := by
  unfold projectedBidirected
  apply Bool.and_eq_true_iff.mpr
  constructor
  · cases equal : Nat.beq left.val right.val with
    | false => rfl
    | true => exact False.elim (different (Fin.ext (Nat.eq_of_beq_eq_true equal)))
  · exact (finAny_eq_true_iff _).mpr
      ⟨root, Bool.and_eq_true_iff.mpr ⟨leftIncident, rightIncident⟩⟩

/-- Deterministically place every root of a canonical extension.  The two
child scans return actual indices; canonical incidence proves that their
routes cover every other selected child.  Hidden common-cause data is read
from the original graph's complete finite search, without choice.

The graph agreement concerns only the bidirected classifier: both models
already share the observed signature and hence the directed projection. -/
def hiddenDAGRootPlacement (latent : LatentExtension S)
    (canonical : latent.CanonicalSemiMarkovian)
    (projected : forall left right,
      latent.projectedBidirected left right = P.observedGraph.bidirected left right)
    (root : Fin latent.count) : HiddenDAGRootPlacement latent P root := by
  cases first : (List.finRange S.count).find? (latent.incident root) with
  | none =>
      apply HiddenDAGRootPlacement.unused
      intro child
      cases incident : latent.incident root child with
      | false => rfl
      | true =>
          exact False.elim ((List.find?_eq_none.mp first) child (List.mem_finRange child) incident)
  | some left =>
      have leftIncident : latent.incident root left = true := List.find?_some first
      cases second : (List.finRange S.count).find? (fun child =>
          latent.incident root child && decide (child ≠ left)) with
      | none =>
          refine .privateInput left leftIncident ?_
          intro child incident
          by_cases equal : child = left
          · exact equal
          · exact False.elim ((List.find?_eq_none.mp second) child (List.mem_finRange child)
              (Bool.and_eq_true_iff.mpr ⟨incident, decide_eq_true equal⟩))
      | some right =>
          have found := Bool.and_eq_true_iff.mp (List.find?_some second)
          have rightIncident : latent.incident root right = true := found.1
          have different : left ≠ right := Ne.symm (of_decide_eq_true found.2)
          have bidirected : P.observedGraph.bidirected left right = true := by
            rw [← projected left right]
            exact latent.projectedBidirected_of_incident root left right different
              leftIncident rightIncident
          let cause := ((P.bidirected_matches left right).mp bidirected).toData
          refine .sharedInput cause.source cause.hidden ?_
          intro child incident
          by_cases atLeft : child = left
          · simpa only [atLeft] using cause.leftPath
          · have atRight : child = right := by
              rcases canonical root left right child leftIncident rightIncident incident with
                  same | same | same
              · exact False.elim (different same)
              · exact False.elim (atLeft same.symm)
              · exact same.symm
            simpa only [atRight] using cause.rightPath

end LatentExtension

namespace FiniteLatentSCM

/-- All input roots of a compatible projected-graph model have internally
constructed original-DAG placement data.  In particular, the positive
countermodels produced by the completeness package satisfy these premises. -/
def hiddenDAGRootPlacements (model : ExactModel S)
    (compatible : Compatible model P.observedGraph) :
    (root : Fin model.latent.count) -> HiddenDAGRootPlacement model.latent P root :=
  model.latent.hiddenDAGRootPlacement compatible.1 compatible.2

end FiniteLatentSCM

namespace FiniteLatentProjection

/-- Every projected observed parent input has an actual hidden-internal
relay path in the original graph.  This supplies the other input family
needed by the reverse model construction, including direct observed edges. -/
def directedPathData (projection : FiniteLatentProjection S) (parent child : Fin S.count)
    (edge : S.directed parent child = true) :
    projection.hiddenDAG.HiddenInternalPathData
      (projection.hiddenDAG.observedNode parent) (projection.hiddenDAG.observedNode child) :=
  ((projection.directed_matches parent child).mp edge).toData

end FiniteLatentProjection
end Causality
end Thesis
