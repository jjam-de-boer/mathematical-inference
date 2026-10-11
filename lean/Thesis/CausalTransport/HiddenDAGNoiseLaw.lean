import Thesis.CausalTransport.HiddenDAGPlacedNoise
import Thesis.Probability.FiniteProductAllocation

namespace Thesis
namespace Causality

open Probability

/-!
# Complete joint law of the allocated original-DAG noise

The nested independent node/root prior is compared with the original model's
prior pushed through the explicit allocation encoding.  This is equality of
probabilities for arbitrary mixed events, not just equality of single-channel
marginals.  Several independent roots may have the same source; their distinct
coordinates and joint law are retained.  Unused roots integrate out by genuine
factor normalization, including when the original graph has no nodes.

The proof first compares every full noise-assignment singleton.  Independent
products are exchanged from node-first to root-first order, and the optional
channel-allocation theorem accounts for each original root.  A singleton's
encoding fibre is a rectangular event in the original root assignment, so the
model's own product law suffices.  Explicit complete finite enumerations then
extend these comparisons to arbitrary events, including zeros.

No denotational soundness theorem is imported, no coupling is supplied as an
external interface, and no positivity, choice or excluded-middle assumption
is added.  Unitwise evaluation preservation can now use this joint law to
compare the complete observable and hard-interventional probability laws.
-/

namespace HiddenDAGPlacedNoise

variable {S : ObservedSignature} {P : FiniteLatentProjection S}

/-- Equality of full node-private vectors is decided by the two explicit
finite coordinate families, not by a classical function-equality instance. -/
private instance noiseAssignmentDecidableEq (model : ExactModel S) :
    DecidableEq ((node : Fin P.hiddenDAG.count) → Row model) :=
  FiniteProduct.assignmentDecidableEq P.hiddenDAG.count (fun _ => Row model)
    (fun _ => rowDecidableEq model)

/-- A full-assignment singleton is the rectangle of its coordinate
singletons.  Function extensionality assembles the supplied finite equalities;
all decisions are the explicit coordinate and assignment instances. -/
private theorem rectangularEvent_singleton (count : Nat) (Value : Fin count → Type u)
    [forall index, DecidableEq (Value index)] [DecidableEq (FiniteProduct.Assignment count Value)]
    (target : FiniteProduct.Assignment count Value) :
    FiniteProduct.rectangularEvent count Value
      (fun index value => decide (value = target index)) = FiniteProbRecord.singletonEvent target := by
  funext candidate
  apply Bool.eq_iff_iff.mpr
  rw [FiniteProduct.rectangularEvent_eq_true_iff]
  change (forall index, decide (candidate index = target index) = true) ↔ decide (candidate = target) = true
  constructor
  · intro same
    exact decide_eq_true (funext (fun index => of_decide_eq_true (same index)))
  · intro same index
    exact decide_eq_true (congrFun (of_decide_eq_true same) index)

/-- Rootwise checks of an encoded vector against a fixed full noise unit.
All nodes of one root column are checked, including every required absence
away from that root's optional owner. -/
private def encodingColumnEvent (model : ExactModel S)
    (compatible : Compatible model P.observedGraph)
    (target : (node : Fin P.hiddenDAG.count) → Row model) (root : Fin model.latent.count)
    (value : model.latent.Value root) : Bool :=
  FiniteProduct.rectangularEvent P.hiddenDAG.count (fun _ => Option (model.latent.Value root))
    (fun node optionValue => decide (optionValue = target node root))
    (FiniteProductAllocation.encode (model.hiddenDAGRootPlacements compatible root).source? value)

/-- The fibre of one full encoded noise unit is a rectangular original-root
event.  The same optional-owner test occurs in both encodings, so no inverse
of the encoding or recovery of unused roots is required. -/
private theorem encodingSingleton_eq_rectangle (model : ExactModel S)
    (compatible : Compatible model P.observedGraph)
    (target : (node : Fin P.hiddenDAG.count) → Row model) :
    (fun roots => FiniteProbRecord.singletonEvent target (encode model compatible roots)) =
      FiniteProduct.rectangularEvent model.latent.count model.latent.Value
        (encodingColumnEvent model compatible target) := by
  funext roots
  apply Bool.eq_iff_iff.mpr
  change decide (encode model compatible roots = target) = true ↔ _
  rw [decide_eq_true_eq, FiniteProduct.rectangularEvent_eq_true_iff]
  constructor
  · intro same root
    apply (FiniteProduct.rectangularEvent_eq_true_iff _ _ _ _).mpr
    intro node
    exact decide_eq_true (congrFun (congrFun same node) root)
  · intro columns
    funext node root
    exact of_decide_eq_true
      ((FiniteProduct.rectangularEvent_eq_true_iff _ _ _ _).mp (columns root) node)

/-- Every complete noise singleton has the same probability in the actual
nested prior and in the original prior's explicit encoded pushforward.
The product exchange compares joint factors, not merely their marginals. -/
theorem prior_singleton_probVal_encode (model : ExactModel S)
    (compatible : Compatible model P.observedGraph)
    (target : (node : Fin P.hiddenDAG.count) → Row model) :
    QProb.Equiv ((prior model compatible).probVal (FiniteProbRecord.singletonEvent target))
      ((model.prior.map (encode model compatible)).probVal (FiniteProbRecord.singletonEvent target)) := by
  let cells := fun node root optionValue => decide (optionValue = target node root)
  let rowEvents := fun node => FiniteProduct.rectangularEvent model.latent.count
    (fun root => Option (model.latent.Value root)) (cells node)
  have rowSingleton (node : Fin P.hiddenDAG.count) :
      rowEvents node = FiniteProbRecord.singletonEvent (target node) :=
    rectangularEvent_singleton _ _ (target node)
  have fullSingleton : FiniteProduct.rectangularEvent P.hiddenDAG.count (fun _ => Row model)
      rowEvents = FiniteProbRecord.singletonEvent target := by
    have sameEvents : rowEvents = (fun node row => decide (row = target node)) := by
      funext node
      exact rowSingleton node
    rw [sameEvents]
    exact rectangularEvent_singleton _ _ target
  have outer := product_law model compatible rowEvents
  rw [fullSingleton] at outer
  have inner := FiniteProduct.qProduct_congr P.hiddenDAG.count (fun node =>
    factor_product_law model compatible node (cells node))
  have exchanged := FiniteProduct.qProduct_exchange P.hiddenDAG.count model.latent.count
    (fun node root => (channelFactor model compatible node root).probVal (cells node root))
  have columns := FiniteProduct.qProduct_congr model.latent.count (fun root =>
    FiniteProductAllocation.channel_rectangular_probVal P.hiddenDAG.count (model.factor root)
      (model.hiddenDAGRootPlacements compatible root).source? (fun node => cells node root))
  have source := model.product_law (encodingColumnEvent model compatible target)
  have mapped := model.prior.map_probVal (encode model compatible) (FiniteProbRecord.singletonEvent target)
  rw [encodingSingleton_eq_rectangle] at mapped
  exact QProb.equiv_trans outer (QProb.equiv_trans inner (QProb.equiv_trans exchanged
    (QProb.equiv_trans columns (QProb.equiv_trans (QProb.equiv_symm source) (QProb.equiv_symm mapped)))))

/-- Complete finite enumeration of the noise alphabet, not just its positive
support.  Deduplication ensures singleton probabilities are summed once. -/
private def noiseAssignments (model : ExactModel S) :
    List ((node : Fin P.hiddenDAG.count) → Row model) :=
  deduplicate (FiniteProduct.enumeration P.hiddenDAG.count (fun _ => Row model)
    (fun _ => rowEnumeration model))

private theorem noiseAssignments_complete (model : ExactModel S)
    (noise : (node : Fin P.hiddenDAG.count) → Row model) : noise ∈ noiseAssignments model := by
  rw [noiseAssignments, mem_deduplicate]
  exact FiniteProduct.enumeration_complete _ _ _ (fun _ => rowEnumeration_complete model) noise

private theorem noiseAssignments_nodup (model : ExactModel S) :
    (noiseAssignments (P := P) model).Nodup :=
  deduplicate_nodup _

/-- The actual allocated prior and the explicitly encoded original prior
agree on every Boolean event over all node/root coordinates.  Zeros and
unused roots are included.  This is the whole joint-noise law needed for
reverse hidden-DAG probability preservation and countermodel lifting. -/
theorem prior_probVal_encode (model : ExactModel S)
    (compatible : Compatible model P.observedGraph)
    (event : ((node : Fin P.hiddenDAG.count) → Row model) → Bool) :
    QProb.Equiv ((prior model compatible).probVal event)
      ((model.prior.map (encode model compatible)).probVal event) :=
  FiniteProbRecord.probVal_extensional_of_singletons
    (prior model compatible) (model.prior.map (encode model compatible))
    (noiseAssignments model) (noiseAssignments_nodup model) (noiseAssignments_complete model)
    (prior_singleton_probVal_encode model compatible) event

end HiddenDAGPlacedNoise
end Causality
end Thesis
