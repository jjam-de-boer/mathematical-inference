import Thesis.CausalTransport.HiddenDAGRootPlacement

namespace Thesis
namespace Causality

open Probability

/-!
# Independent finite private-noise vectors at the allocated hidden-DAG nodes

Several canonical input roots may be placed at the same original hidden
common ancestor.  That node must carry distinct independent channels, with
their original root-factor laws.  Reusing a single bit for those channels
would change the countermodel.  Here each node receives an actual dependent
product record over all root slots: allocated slots contain their original
root values, and all other slots are deterministically `none`.

The outer product makes different nodes' private vectors independent; the
inner product makes different allocated root channels independent even at
one node.  Both product laws are proved for arbitrary rectangular events.
The original law of every allocated channel is also proved as a marginal
of the complete outer prior, not merely stipulated in a factor field.

`none` records an absent channel, not a probability value or a default root
value.  Thus no root alphabet inhabitant is selected, observational zeros
and zero-weight noise atoms remain allowed, and empty root/node products
retain their unique empty assignment.  These are genuine probability data
for the reverse construction.  `HiddenDAGRealization` supplies its typed relay
mechanisms and `HiddenDAGEvaluation` proves unitwise evaluation preservation.
`HiddenDAGNoiseLaw` proves equality of the complete grouped-noise probability
law with the encoded original prior.  `HiddenDAGProbability` consequently
preserves all original-DAG observable/interventional event probabilities.
-/

namespace HiddenDAGPlacedNoise

variable {S : ObservedSignature} {P : FiniteLatentProjection S}

/-- A node's channel vector retains the original root slots and their
possibly different finite alphabets.  Missing slots require no chosen value. -/
abbrev Row (model : ExactModel S) :=
  (root : Fin model.latent.count) -> Option (model.latent.Value root)

instance rowDecidableEq (model : ExactModel S) : DecidableEq (Row model) :=
  FiniteProduct.assignmentDecidableEq model.latent.count
    (fun root => Option (model.latent.Value root)) (fun _ => inferInstance)

/-- The complete finite option presentation, including absent channels.
This presentation is not the support of the probability law: many of its
values have zero mass in a particular placed vector. -/
def rowEnumeration (model : ExactModel S) : List (Row model) :=
  FiniteProduct.enumeration model.latent.count
    (fun root => Option (model.latent.Value root))
    (fun root => none :: (model.latent.valueEnumeration root).map some)

theorem rowEnumeration_complete (model : ExactModel S) (row : Row model) :
    row ∈ rowEnumeration model := by
  apply FiniteProduct.enumeration_complete
  intro root value
  cases value with
  | none => exact List.mem_cons.mpr (Or.inl rfl)
  | some value =>
      exact List.mem_cons.mpr (Or.inr
        (List.mem_map.mpr ⟨value, model.latent.value_complete root value, rfl⟩))

/-- The absent channel has one actual atom and unit total mass.  This
construction is available even for an empty original root value type. -/
private def absentChannel (Value : Type u) : FiniteProbRecord (Option Value) where
  atoms := [(none, 1)]
  den := 1
  den_pos := Nat.zero_lt_one
  total_mass := rfl

/-- Preserve the original factor exactly at its one allocated source;
unallocated slots are deterministic absence, not fresh copies of the root. -/
def channelFactor (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (node : Fin P.hiddenDAG.count) (root : Fin model.latent.count) :
    FiniteProbRecord (Option (model.latent.Value root)) :=
  if (model.hiddenDAGRootPlacements compatible root).source? = some node then
    (model.factor root).map some
  else absentChannel (model.latent.Value root)

/-- An actual node-private vector law, with independent allocated channels.
Independent copies are not added at relay nodes: their slots are absent. -/
def factor (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (node : Fin P.hiddenDAG.count) : FiniteProbRecord (Row model) :=
  FiniteProduct.record model.latent.count
    (fun root => Option (model.latent.Value root)) (channelFactor model compatible node)

/-- The full independent private-noise law over the original graph's nodes.
Node and root factors retain their supplied positive total denominators;
individual atoms are not required to have positive weights. -/
def prior (model : ExactModel S) (compatible : Compatible model P.observedGraph) :
    FiniteProbRecord ((node : Fin P.hiddenDAG.count) -> Row model) :=
  FiniteProduct.record P.hiddenDAG.count (fun _ => Row model) (factor model compatible)

/-- Complete channel independence within one node, for arbitrary events in
each root alphabet.  The proof concerns the actual constructed factor record. -/
theorem factor_product_law (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (node : Fin P.hiddenDAG.count)
    (events : (root : Fin model.latent.count) -> Option (model.latent.Value root) -> Bool) :
    QProb.Equiv
      ((factor model compatible node).probVal
        (FiniteProduct.rectangularEvent model.latent.count
          (fun root => Option (model.latent.Value root)) events))
      (FiniteProduct.qProduct model.latent.count
        (fun root => (channelFactor model compatible node root).probVal (events root))) :=
  FiniteProduct.record_rectangular_probVal _ _ _ events

/-- Complete node-private independence, in precisely the shape needed by
`FiniteHiddenDAGSCM.product_law`.  No independence assumption is supplied by
the caller beyond the original model's already existing factor data. -/
theorem product_law (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (events : (node : Fin P.hiddenDAG.count) -> Row model -> Bool) :
    QProb.Equiv
      ((prior model compatible).probVal
        (FiniteProduct.rectangularEvent P.hiddenDAG.count (fun _ => Row model) events))
      (FiniteProduct.qProduct P.hiddenDAG.count
        (fun node => (factor model compatible node).probVal (events node))) :=
  FiniteProduct.record_rectangular_probVal _ _ _ events

/-- At an allocated source, arbitrary channel events have their original
root-factor probability.  The option merely records presence of that value. -/
theorem channelFactor_probVal_of_placed
    (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (node : Fin P.hiddenDAG.count) (root : Fin model.latent.count)
    (placed : (model.hiddenDAGRootPlacements compatible root).source? = some node)
    (event : Option (model.latent.Value root) -> Bool) :
    QProb.Equiv ((channelFactor model compatible node root).probVal event)
      ((model.factor root).probVal (fun value => event (some value))) := by
  rw [channelFactor, if_pos placed]
  exact (model.factor root).map_probVal some event

/-- Read an allocated channel from the *whole* original-node noise prior.
Outer and inner coordinate marginal laws prove that grouping roots at the
same node has not changed the selected channel's original factor law. -/
theorem prior_channel_probVal_of_placed
    (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (node : Fin P.hiddenDAG.count) (root : Fin model.latent.count)
    (placed : (model.hiddenDAGRootPlacements compatible root).source? = some node)
    (event : Option (model.latent.Value root) -> Bool) :
    QProb.Equiv ((prior model compatible).probVal (fun noise => event (noise node root)))
      ((model.factor root).probVal (fun value => event (some value))) :=
  QProb.equiv_trans
    (FiniteProduct.record_coordinate_probVal_dependent P.hiddenDAG.count (fun _ => Row model)
      (factor model compatible) node (fun row => event (row root)))
    (QProb.equiv_trans
      (FiniteProduct.record_coordinate_probVal_dependent model.latent.count
        (fun root => Option (model.latent.Value root)) (channelFactor model compatible node) root event)
      (channelFactor_probVal_of_placed model compatible node root placed event))

/-- Encode an original root assignment into the allocated node-private
vectors.  This is an explicit function, not a chosen probabilistic coupling;
its complete probability law is proved separately in `HiddenDAGNoiseLaw`. -/
def encode (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (roots : model.latent.Assignment) : (node : Fin P.hiddenDAG.count) -> Row model :=
  fun node root => if (model.hiddenDAGRootPlacements compatible root).source? = some node
    then some (roots root) else none

/-- Every allocated coordinate reads the exact original value under the
explicit encoding.  Unused inputs and unrelated nodes require no default. -/
theorem encode_of_placed (model : ExactModel S) (compatible : Compatible model P.observedGraph)
    (roots : model.latent.Assignment) (node : Fin P.hiddenDAG.count) (root : Fin model.latent.count)
    (placed : (model.hiddenDAGRootPlacements compatible root).source? = some node) :
    encode model compatible roots node root = some (roots root) :=
  if_pos placed

end HiddenDAGPlacedNoise
end Causality
end Thesis
