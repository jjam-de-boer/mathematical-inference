import Thesis.CausalTransport.HedgePartialIncidence
import Thesis.Probability.BooleanNoise

namespace Thesis
namespace Causality

open Probability

/-!
# Exact cancellation of a partially selected independent hedge channel

A channel supplies an independent fair bit at each bidirected pair root.
Its local incidence character is read at some vertices of a connected
component.  Reading the entire component gives even parity by the finite
handshaking identity.  Reading a nonempty proper subset instead gives a fair
parity: an explicit XOR translation exchanges its two equally sized fibres.

The translation below is computed by the existing constructive incidence
solver.  A selected vertex and an excluded component vertex are supplied as
data, so no representative is extracted from an existential proposition.
The proof permutes the full pair-root enumeration symbolically; no concrete
exponential list is evaluated while checking these general declarations.

This is the orthogonality leaf for the multi-channel table construction.
In a product expansion, a partially selected connected channel cancels,
whereas a wholly selected channel retains its local observed character.
`HedgeChannelIntegration` assembles the actual independent block integration;
`HedgeChannelPairRoot` transports it to the original pair-root source grouping.
This one-channel marginal law alone is not mistaken for independence of an
arbitrary family or for an observational countermodel.
-/

variable {S : ObservedSignature}

/-- Incidence parity read only at the tested vertices, while pair-root
incidence itself belongs to the full designated component. -/
def hedgeChannelIncidenceParity (G : ObservedGraph S) (nodes tested : NodeSet S)
    (pairBits : Fin (pairRootCount G) -> Bool) : Bool :=
  hedgeNodeXor tested (fun node => hedgeXorPairBitsWithinFrom G nodes node pairBits)

/-- Translating pair-root bits translates the tested character by XOR. -/
theorem hedgeChannelIncidenceParity_xor (G : ObservedGraph S) (nodes tested : NodeSet S)
    (left right : Fin (pairRootCount G) -> Bool) :
    hedgeChannelIncidenceParity G nodes tested (hedgePairBitsXor G left right) =
      Bool.xor (hedgeChannelIncidenceParity G nodes tested left)
        (hedgeChannelIncidenceParity G nodes tested right) := by
  unfold hedgeChannelIncidenceParity hedgeNodeXor
  have expanded := foldl_congr
    (fun total node => Bool.xor total
      (hedgeXorPairBitsWithinFrom G nodes node (hedgePairBitsXor G left right)))
    (fun total node => Bool.xor total (Bool.xor
      (hedgeXorPairBitsWithinFrom G nodes node left) (hedgeXorPairBitsWithinFrom G nodes node right)))
    false (NodeSet.members tested) (fun total node => by
      exact congrArg (Bool.xor total) (hedgeXorPairBitsWithinFrom_xor G nodes node left right))
  exact expanded.trans (foldl_xor_pointwise _ _ _)

/-- A complete channel has even incidence regardless of the pair bits.
Connectivity is unnecessary for this direction of the handshaking law. -/
theorem hedgeChannelIncidenceParity_full (G : ObservedGraph S) (nodes : NodeSet S)
    (pairBits : Fin (pairRootCount G) -> Bool) :
    hedgeChannelIncidenceParity G nodes nodes pairBits = false :=
  hedgeNodeXor_incidence G nodes pairBits

/-- Compute one fixed vector that flips the tested channel parity.  Its
balancing vertex is outside the tested set but inside the full component. -/
def BidirectedComponent.channelParityFlipPairBits (G : ObservedGraph S) (nodes : NodeSet S)
    (component : BidirectedComponent G nodes) (balance : Fin S.count) (inside : nodes balance = true)
    (pivot : Fin S.count) : Fin (pairRootCount G) -> Bool :=
  component.partialTargetPairBits G nodes balance inside (fun node => decide (node = pivot))

/-- The fixed translation has odd tested parity: the selected pivot occurs
once, and the balancing correction is never read by the tested character. -/
theorem BidirectedComponent.channelParityFlipPairBits_spec
    (G : ObservedGraph S) (nodes tested : NodeSet S) (component : BidirectedComponent G nodes)
    (subset : NodeSet.Subset tested nodes) (balance : Fin S.count) (inside : nodes balance = true)
    (excluded : tested balance = false) (pivot : Fin S.count) (selected : tested pivot = true) :
    hedgeChannelIncidenceParity G nodes tested
      (component.channelParityFlipPairBits G nodes balance inside pivot) = true := by
  unfold hedgeChannelIncidenceParity hedgeNodeXor
  have same := foldl_congr_of_mem
    (fun total node => Bool.xor total (hedgeXorPairBitsWithinFrom G nodes node
      (component.channelParityFlipPairBits G nodes balance inside pivot)))
    (fun total node => Bool.xor total (decide (node = pivot))) false (NodeSet.members tested)
    (fun total node member => by
      exact congrArg (Bool.xor total)
        (component.partialTargetPairBits_spec G nodes tested subset balance inside excluded
          (fun index => decide (index = pivot)) node ((NodeSet.mem_members_iff tested node).mp member)))
  exact same.trans (foldl_xor_indicator_of_mem_nodup (NodeSet.members tested) pivot
    ((NodeSet.mem_members_iff tested pivot).mpr selected) (NodeSet.nodup_members tested))

/-- Actual finite fibre counts are equal for every nonempty proper tested
subset of a connected component.  A fixed observed/parent phase is harmless:
the same translation still exchanges the phase-shifted parity and its negation. -/
theorem BidirectedComponent.channelParity_counts_equal
    (G : ObservedGraph S) (nodes tested : NodeSet S) (component : BidirectedComponent G nodes)
    (subset : NodeSet.Subset tested nodes) (balance : Fin S.count) (inside : nodes balance = true)
    (excluded : tested balance = false) (pivot : Fin S.count) (selected : tested pivot = true)
    (phase : Bool) :
    ((hedgePairBitEnum G).filter (fun pairBits =>
      Bool.xor phase (hedgeChannelIncidenceParity G nodes tested pairBits))).length =
    ((hedgePairBitEnum G).filter (fun pairBits =>
      !(Bool.xor phase (hedgeChannelIncidenceParity G nodes tested pairBits)))).length := by
  let delta := component.channelParityFlipPairBits G nodes balance inside pivot
  let event := fun pairBits => Bool.xor phase (hedgeChannelIncidenceParity G nodes tested pairBits)
  have flipped : forall pairBits, event (hedgePairBitsXor G pairBits delta) = !(event pairBits) := by
    intro pairBits
    unfold event
    rw [hedgeChannelIncidenceParity_xor,
      component.channelParityFlipPairBits_spec G nodes tested subset balance inside excluded pivot selected]
    cases phase <;> cases hedgeChannelIncidenceParity G nodes tested pairBits <;> rfl
  have permutation := (hedgePairBitEnum_map_xor_perm G delta).filter event
  have predicate : event ∘ (fun pairBits => hedgePairBitsXor G pairBits delta) =
      (fun pairBits => !(event pairBits)) := funext flipped
  rw [List.filter_map, predicate] at permutation
  exact permutation.length_eq.symm.trans (List.length_map _)

/-- One independent fair pair-bit block as an actual finite record.  An
explicit all-zero vector proves nonempty support without selecting an atom. -/
def hedgeChannelPairBitRecord (G : ObservedGraph S) : FiniteProbRecord (Fin (pairRootCount G) -> Bool) where
  atoms := (hedgePairBitEnum G).map (fun bits => (bits, 1))
  den := (hedgePairBitEnum G).length
  den_pos := by
    have member := hedgePairBitEnum_complete G (hedgeZeroPairBits G)
    cases enumeration : hedgePairBitEnum G with
    | nil => rw [enumeration] at member; cases member
    | cons head tail => simp only [List.length_cons]; omega
  total_mass := FiniteProbRecord.totalMass_unit _

/-- The proper-subset character is fair under the normalized pair-bit
record, with every parent phase included.  This is an exact probability
identity, not just an informal cancellation of signed terms. -/
theorem BidirectedComponent.channelParity_probVal_half
    (G : ObservedGraph S) (nodes tested : NodeSet S) (component : BidirectedComponent G nodes)
    (subset : NodeSet.Subset tested nodes) (balance : Fin S.count) (inside : nodes balance = true)
    (excluded : tested balance = false) (pivot : Fin S.count) (selected : tested pivot = true)
    (phase : Bool) :
    QProb.Equiv ((hedgeChannelPairBitRecord G).probVal (fun pairBits =>
      Bool.xor phase (hedgeChannelIncidenceParity G nodes tested pairBits))) ⟨1, 2, by decide⟩ := by
  let event := fun pairBits => Bool.xor phase (hedgeChannelIncidenceParity G nodes tested pairBits)
  have counts := component.channelParity_counts_equal G nodes tested subset balance inside excluded pivot selected phase
  have equalMass : FiniteProbRecord.eventMass (hedgeChannelPairBitRecord G).atoms event =
      FiniteProbRecord.eventMass (hedgeChannelPairBitRecord G).atoms (fun bits => !(event bits)) := by
    rw [hedgeChannelPairBitRecord, FiniteProbRecord.eventMass_unit, FiniteProbRecord.eventMass_unit]
    simpa only [count, List.countP_eq_length_filter] using counts
  have total := FiniteProbRecord.eventMass_add_complement (hedgeChannelPairBitRecord G).atoms event
  rw [← equalMass, (hedgeChannelPairBitRecord G).total_mass] at total
  change FiniteProbRecord.eventMass (hedgeChannelPairBitRecord G).atoms event * 2 =
    1 * (hedgeChannelPairBitRecord G).den
  omega

end Causality
end Thesis
