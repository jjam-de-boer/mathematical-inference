import Thesis.CausalTransport.HedgeChannelOrthogonality
import Thesis.Probability.FiniteSignedProduct

namespace Thesis
namespace Causality

open Probability

/-!
# Exact integration of independent finite hedge-channel characters

The local numerator expansion chooses a channel term at each free row.
Grouping one monomial by channel gives a product of incidence characters.
Its integral must use the joint independent record, not marginal fairness
alone.  This module builds that actual product record and proves exact signed
integration and cancellation for arbitrary finite channel families.

The channel-major record below is a probability presentation of pair bits,
not a new shared SCM source incident to every vertex.  Realizing its transpose
as independent pair-root sources with the original graph incidence remains
a separate construction.  In particular this presentation cannot be used
to add an inadmissible common mixing variable to a hedge countermodel.

A nonempty proper selected subset in any one connected channel makes the
entire monomial integral zero.  Other channels can have arbitrary selections,
phases and components.  Completely selected channels retain their phase
with the correct total natural mass.  All statements retain the actual
record denominators and introduce no infinite or approximate integration.
-/

variable {S : ObservedSignature}

/-- The genuinely independent product of the individual pair-bit records.
This is a prior presentation, not a graph-incidence declaration for an SCM. -/
def hedgeChannelBlocksRecord (G : ObservedGraph S) (count : Nat) :
    FiniteProbRecord (Fin count -> Fin (pairRootCount G) -> Bool) :=
  FiniteProduct.record count (fun _ => Fin (pairRootCount G) -> Bool) (fun _ => hedgeChannelPairBitRecord G)

/-- Proper-subset orthogonality at the exact signed natural atom mass.
The two ordinary event fibres have been proved equal constructively. -/
theorem BidirectedComponent.channelSignedMass_zero
    (G : ObservedGraph S) (nodes tested : NodeSet S) (component : BidirectedComponent G nodes)
    (subset : NodeSet.Subset tested nodes) (balance : Fin S.count) (inside : nodes balance = true)
    (excluded : tested balance = false) (pivot : Fin S.count) (selected : tested pivot = true) (phase : Bool) :
    (hedgeChannelPairBitRecord G).signedMass (fun pairBits => FiniteProbRecord.characterSign
      (Bool.xor phase (hedgeChannelIncidenceParity G nodes tested pairBits))) = 0 := by
  apply FiniteProbRecord.signedMass_character_zero
  have counts := component.channelParity_counts_equal G nodes tested subset balance inside excluded pivot selected phase
  rw [hedgeChannelPairBitRecord, FiniteProbRecord.eventMass_unit, FiniteProbRecord.eventMass_unit]
  simpa only [count, List.countP_eq_length_filter] using counts.symm

/-- Full incidence has sign one, so an observed/parent phase contributes
its sign times the actual total mass of the one-channel record. -/
theorem hedgeChannelSignedMass_full (G : ObservedGraph S) (nodes : NodeSet S) (phase : Bool) :
    (hedgeChannelPairBitRecord G).signedMass (fun pairBits => FiniteProbRecord.characterSign
      (Bool.xor phase (hedgeChannelIncidenceParity G nodes nodes pairBits))) =
      ((hedgeChannelPairBitRecord G).den : Int) * FiniteProbRecord.characterSign phase := by
  have constant := FiniteProbRecord.signedAtomMass_congr (hedgeChannelPairBitRecord G).atoms
    (fun pairBits => FiniteProbRecord.characterSign (Bool.xor phase (hedgeChannelIncidenceParity G nodes nodes pairBits)))
    (fun _ => FiniteProbRecord.characterSign phase) (fun pairBits => by
      change FiniteProbRecord.characterSign (Bool.xor phase (hedgeChannelIncidenceParity G nodes nodes pairBits)) =
        FiniteProbRecord.characterSign phase
      rw [hedgeChannelIncidenceParity_full, Bool.xor_false])
  exact constant.trans ((hedgeChannelPairBitRecord G).signedMass_const _)

/-- The complete monomial integral is the product of the individual
integrals against their independent natural-weight records. -/
theorem hedgeChannelBlocks_signedMass (G : ObservedGraph S) (count : Nat)
    (nodes tested : Fin count -> NodeSet S) (phase : Fin count -> Bool) :
    (hedgeChannelBlocksRecord G count).signedMass (fun blocks => FiniteProduct.iProduct count
      (fun channel => FiniteProbRecord.characterSign
        (Bool.xor (phase channel) (hedgeChannelIncidenceParity G (nodes channel) (tested channel) (blocks channel))))) =
      FiniteProduct.iProduct count (fun channel => (hedgeChannelPairBitRecord G).signedMass
        (fun bits => FiniteProbRecord.characterSign
          (Bool.xor (phase channel) (hedgeChannelIncidenceParity G (nodes channel) (tested channel) bits)))) :=
  FiniteProduct.record_signedMass_rectangular count
    (fun _ => Fin (pairRootCount G) -> Bool)
    (fun _ => hedgeChannelPairBitRecord G)
    (fun channel bits => FiniteProbRecord.characterSign
      (Bool.xor (phase channel) (hedgeChannelIncidenceParity G (nodes channel) (tested channel) bits)))

/-- Any proper nonempty connected channel cancels the entire independent
monomial.  No assumptions are made about the selections of other channels. -/
theorem hedgeChannelBlocks_signedMass_zero (G : ObservedGraph S) (count : Nat)
    (nodes tested : Fin count -> NodeSet S) (phase : Fin count -> Bool) (chosen : Fin count)
    (component : BidirectedComponent G (nodes chosen))
    (subset : NodeSet.Subset (tested chosen) (nodes chosen))
    (balance : Fin S.count) (inside : nodes chosen balance = true) (excluded : tested chosen balance = false)
    (pivot : Fin S.count) (selected : tested chosen pivot = true) :
    (hedgeChannelBlocksRecord G count).signedMass (fun blocks => FiniteProduct.iProduct count
      (fun channel => FiniteProbRecord.characterSign
        (Bool.xor (phase channel) (hedgeChannelIncidenceParity G (nodes channel) (tested channel) (blocks channel))))) = 0 := by
  rw [hedgeChannelBlocks_signedMass]
  apply FiniteProduct.iProduct_eq_zero count _ chosen
  exact component.channelSignedMass_zero G _ _ subset balance inside excluded pivot selected (phase chosen)

/-- The fully selected monomial keeps every phase and the full product
of record masses.  Its coefficient must still be matched to the competing
small-channel term when assembling observationally equal SCM tables. -/
theorem hedgeChannelBlocks_signedMass_full (G : ObservedGraph S) (count : Nat)
    (nodes : Fin count -> NodeSet S) (phase : Fin count -> Bool) :
    (hedgeChannelBlocksRecord G count).signedMass (fun blocks => FiniteProduct.iProduct count
      (fun channel => FiniteProbRecord.characterSign
        (Bool.xor (phase channel) (hedgeChannelIncidenceParity G (nodes channel) (nodes channel) (blocks channel))))) =
      FiniteProduct.iProduct count (fun channel => ((hedgeChannelPairBitRecord G).den : Int) *
        FiniteProbRecord.characterSign (phase channel)) := by
  rw [hedgeChannelBlocks_signedMass]
  exact FiniteProduct.iProduct_congr count _ _ (fun channel => hedgeChannelSignedMass_full G (nodes channel) (phase channel))

end Causality
end Thesis
