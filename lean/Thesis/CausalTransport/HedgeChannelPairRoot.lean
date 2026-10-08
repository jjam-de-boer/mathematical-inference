import Thesis.CausalTransport.HedgeChannelIntegration
import Thesis.Causality.PairRootChannels

namespace Thesis
namespace Causality
namespace PairRootChannels

open Probability

/-!
# Whole-prior transport from actual pair roots to channel blocks

`PairRootChannels.prior` is the graph-compatible root-major product: one
independent channel vector at each actual bidirected pair root.  The channel
cancellation calculation instead uses `hedgeChannelBlocksRecord`, whose
coordinates are complete pair-bit blocks.  Neither a common global source
nor marginal fairness alone can justify identifying these presentations.

The explicit matrix transpose below permutes their complete unit-weight
enumerations.  It therefore preserves every mixed event and every finite
integer-valued integrand, with equal literal denominators.  The independent
block integration and proper-subset cancellation are then transported to the
actual pair-root prior rather than assumed for an arbitrary correlated law.

The last local bridge restricts channel reads to a mechanism's incident
inputs.  Nonincident roots are padded with zero only for expressing the same
incidence fold; their values are never made available to a local mechanism.
Graph-specific positive row coefficients and the two countermodel laws
remain separate constructive obligations.
-/

variable {S : ObservedSignature}

/-- Channel-major support used by the existing independent block record. -/
def blockEnumeration (G : ObservedGraph S) (channels : Nat) :
    List (Fin channels -> Fin (pairRootCount G) -> Bool) :=
  FiniteProduct.enumeration channels (fun _ => Fin (pairRootCount G) -> Bool) (fun _ => hedgePairBitEnum G)

/-- Every full channel-by-root matrix occurs in the block presentation. -/
theorem blockEnumeration_complete (G : ObservedGraph S) (channels : Nat)
    (blocks : Fin channels -> Fin (pairRootCount G) -> Bool) : blocks ∈ blockEnumeration G channels :=
  FiniteProduct.enumeration_complete channels (fun _ => Fin (pairRootCount G) -> Bool)
    (fun _ => hedgePairBitEnum G) (fun _ => hedgePairBitEnum_complete G) blocks

/-- Complete blocks occur once because each coordinate block occurs once. -/
theorem blockEnumeration_nodup (G : ObservedGraph S) (channels : Nat) : (blockEnumeration G channels).Nodup :=
  FiniteProduct.enumeration_nodup channels (fun _ => Fin (pairRootCount G) -> Bool)
    (fun _ => hedgePairBitEnum G)
    (fun _ => FiniteProduct.assignmentDecidableEq (pairRootCount G) (fun _ => Bool) (fun _ => inferInstance))
    (fun _ => hedgePairBitEnum_nodup G)

/-- The block presentation also has literal unit weights, not merely the
same possible matrix entries as the actual root-major prior. -/
theorem blocksRecord_atoms (G : ObservedGraph S) (channels : Nat) :
    (hedgeChannelBlocksRecord G channels).atoms = (blockEnumeration G channels).map (fun blocks => (blocks, 1)) :=
  FiniteProduct.record_atoms_eq_unit channels (fun _ => Fin (pairRootCount G) -> Bool)
    (fun _ => hedgeChannelPairBitRecord G) (fun _ => hedgePairBitEnum G) (fun _ => rfl)

/-- The independent block record keeps the full unit-support normalization. -/
theorem blocksRecord_den (G : ObservedGraph S) (channels : Nat) :
    (hedgeChannelBlocksRecord G channels).den = (blockEnumeration G channels).length :=
  FiniteProduct.record_den_eq_length channels (fun _ => Fin (pairRootCount G) -> Bool)
    (fun _ => hedgeChannelPairBitRecord G) (fun _ => hedgePairBitEnum G) (fun _ => rfl)

/-- Transposing the root-major support gives exactly a permutation of the
complete block support.  Both inverses are explicit matrix reads, so the
proof selects no latent assignment or probabilistic coupling. -/
theorem enumeration_channelBits_perm (G : ObservedGraph S) (channels : Nat) :
    ((enumeration G channels).map (channelBits G channels)).Perm (blockEnumeration G channels) := by
  letI : DecidableEq (Fin channels -> Fin (pairRootCount G) -> Bool) :=
    FiniteProduct.assignmentDecidableEq channels (fun _ => Fin (pairRootCount G) -> Bool)
      (fun _ => FiniteProduct.assignmentDecidableEq (pairRootCount G) (fun _ => Bool) (fun _ => inferInstance))
  apply ConstructivePermutation.perm_of_nodup_mem_iff
  · apply ConstructivePermutation.nodup_map_of_injective_on
    · intro left _leftMem right _rightMem equal
      exact congrArg (fromChannelBits G channels) equal
    · exact enumeration_nodup G channels
  · exact blockEnumeration_nodup G channels
  · intro blocks
    constructor
    · intro _member
      exact blockEnumeration_complete G channels blocks
    · intro _member
      exact List.mem_map.mpr ⟨fromChannelBits G channels blocks,
        enumeration_complete G channels _, channelBits_fromChannelBits G channels blocks⟩

/-- Reindexing preserves the literal normalization mass, including empty
root or channel families; no nonzero probability cell is divided out. -/
theorem prior_den_eq_blocks (G : ObservedGraph S) (channels : Nat) :
    (prior G channels).den = (hedgeChannelBlocksRecord G channels).den := by
  rw [prior_den, blocksRecord_den]
  have lengths := (enumeration_channelBits_perm G channels).length_eq
  simpa only [List.length_map] using lengths

/-- Every mixed event has the same probability after transposing the actual
pair-root prior.  This supplies whole-law transport, not only rectangles. -/
theorem prior_probVal_channelBits (G : ObservedGraph S) (channels : Nat)
    (event : Event (Fin channels -> Fin (pairRootCount G) -> Bool)) :
    QProb.Equiv ((prior G channels).probVal (fun assignment => event (channelBits G channels assignment)))
      ((hedgeChannelBlocksRecord G channels).probVal event) := by
  change FiniteProbRecord.eventMass (prior G channels).atoms _ * (hedgeChannelBlocksRecord G channels).den =
    FiniteProbRecord.eventMass (hedgeChannelBlocksRecord G channels).atoms event * (prior G channels).den
  rw [prior_atoms, blocksRecord_atoms,
    FiniteProbRecord.eventMass_unit_reindex _ _ _ (enumeration_channelBits_perm G channels) event,
    prior_den_eq_blocks]

/-- Every finite signed integral is preserved on the actual natural weights.
Its normalizing mass is separately identified by `prior_den_eq_blocks`. -/
theorem prior_signedMass_channelBits (G : ObservedGraph S) (channels : Nat)
    (integrand : (Fin channels -> Fin (pairRootCount G) -> Bool) -> Int) :
    (prior G channels).signedMass (fun assignment => integrand (channelBits G channels assignment)) =
      (hedgeChannelBlocksRecord G channels).signedMass integrand := by
  change FiniteProbRecord.signedAtomMass (prior G channels).atoms _ =
    FiniteProbRecord.signedAtomMass (hedgeChannelBlocksRecord G channels).atoms integrand
  rw [prior_atoms, blocksRecord_atoms]
  exact FiniteProbRecord.signedAtomMass_unit_reindex _ _ _ (enumeration_channelBits_perm G channels) integrand

/-- Independent-channel integration now holds against the actual SCM source
grouping.  A channel bit is read from its own original pair root. -/
theorem prior_character_signedMass (G : ObservedGraph S) (channels : Nat)
    (nodes tested : Fin channels -> NodeSet S) (phase : Fin channels -> Bool) :
    (prior G channels).signedMass (fun assignment => FiniteProduct.iProduct channels
      (fun channel => FiniteProbRecord.characterSign (Bool.xor (phase channel)
        (hedgeChannelIncidenceParity G (nodes channel) (tested channel)
          (fun root => assignment root channel))))) =
      FiniteProduct.iProduct channels (fun channel => (hedgeChannelPairBitRecord G).signedMass
        (fun bits => FiniteProbRecord.characterSign
          (Bool.xor (phase channel) (hedgeChannelIncidenceParity G (nodes channel) (tested channel) bits)))) :=
  (prior_signedMass_channelBits G channels _).trans (hedgeChannelBlocks_signedMass G channels nodes tested phase)

/-- A proper nonempty connected channel cancels its entire monomial under
the actual pair-root prior, regardless of the other channel selections. -/
theorem prior_character_signedMass_zero (G : ObservedGraph S) (channels : Nat)
    (nodes tested : Fin channels -> NodeSet S) (phase : Fin channels -> Bool) (chosen : Fin channels)
    (component : BidirectedComponent G (nodes chosen))
    (subset : NodeSet.Subset (tested chosen) (nodes chosen))
    (balance : Fin S.count) (inside : nodes chosen balance = true) (excluded : tested chosen balance = false)
    (pivot : Fin S.count) (selected : tested chosen pivot = true) :
    (prior G channels).signedMass (fun assignment => FiniteProduct.iProduct channels
      (fun channel => FiniteProbRecord.characterSign (Bool.xor (phase channel)
        (hedgeChannelIncidenceParity G (nodes channel) (tested channel)
          (fun root => assignment root channel))))) = 0 :=
  (prior_signedMass_channelBits G channels _).trans
    (hedgeChannelBlocks_signedMass_zero G channels nodes tested phase chosen component subset balance inside excluded pivot selected)

/-- Fully selected channels retain exactly the same phase and normalization
coefficient after realizing them at the actual pair-root sources. -/
theorem prior_character_signedMass_full (G : ObservedGraph S) (channels : Nat)
    (nodes : Fin channels -> NodeSet S) (phase : Fin channels -> Bool) :
    (prior G channels).signedMass (fun assignment => FiniteProduct.iProduct channels
      (fun channel => FiniteProbRecord.characterSign (Bool.xor (phase channel)
        (hedgeChannelIncidenceParity G (nodes channel) (nodes channel)
          (fun root => assignment root channel))))) =
      FiniteProduct.iProduct channels (fun channel => ((hedgeChannelPairBitRecord G).den : Int) *
        FiniteProbRecord.characterSign (phase channel)) :=
  (prior_signedMass_channelBits G channels _).trans (hedgeChannelBlocks_signedMass_full G channels nodes phase)

/-- A typed mechanism can access only incident root values.  Padding the
other slots with zero is notation for a local incidence read, not access to
the complete shared assignment or an extra global hidden source. -/
def inputPairBits (G : ObservedGraph S) (channels : Nat) (child : Fin S.count)
    (inputs : (extension G channels).Inputs child) (channel : Fin channels) : Fin (pairRootCount G) -> Bool :=
  fun root => if selected : pairRootIncident G root child = true then inputs root selected channel else false

/-- Local incidence character computed solely from declared shared inputs. -/
def inputIncidence (G : ObservedGraph S) (channels : Nat) (nodes : NodeSet S) (child : Fin S.count)
    (inputs : (extension G channels).Inputs child) (channel : Fin channels) : Bool :=
  hedgeXorPairBitsWithinFrom G nodes child (inputPairBits G channels child inputs channel)

/-- Supplying a real shared assignment to the typed local input map gives
exactly its global incidence character.  Nonincident coordinates disappear
because the fold does not read them, not because their bits are assumed zero. -/
theorem inputIncidence_assignment (G : ObservedGraph S) (channels : Nat) (nodes : NodeSet S)
    (child : Fin S.count) (assignment : (extension G channels).Assignment) (channel : Fin channels) :
    inputIncidence G channels nodes child (fun root _incident => assignment root) channel =
      hedgeXorPairBitsWithinFrom G nodes child (fun root => assignment root channel) := by
  unfold inputIncidence hedgeXorPairBitsWithinFrom
  apply foldl_congr
  intro total root
  change (if hedgeIncident G (hedgePairRoot G root) child && hedgePairRootWithin G nodes root then
    Bool.xor total (inputPairBits G channels child (fun root _incident => assignment root) channel root) else total) =
      (if hedgeIncident G (hedgePairRoot G root) child && hedgePairRootWithin G nodes root then
        Bool.xor total (assignment root channel) else total)
  simp only [hedgeIncident_pair]
  cases incident : pairRootIncident G root child with
  | false => simp only [Bool.false_and, Bool.false_eq_true, if_false]
  | true =>
      have localBit : inputPairBits G channels child (fun root _incident => assignment root) channel root =
          assignment root channel := by
        unfold inputPairBits
        rw [dif_pos incident]
      rw [localBit]

end PairRootChannels
end Causality
end Thesis
