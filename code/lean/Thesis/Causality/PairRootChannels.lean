import Thesis.Causality.PairRoot
import Thesis.Probability.FiniteUniformProduct

namespace Thesis
namespace Causality
namespace PairRootChannels

open Probability

/-!
# Independent finite channel vectors at the actual pair roots

A channel-major matrix is useful for the cancellation proof, but it must not
be installed as one hidden source incident to an entire hedge.  Here every
original bidirected pair retains its own root and precisely its two original
children.  Its alphabet is a finite vector of independent fair channel bits.
Different pair roots are independent under the actual product prior.

The construction works for any finite number of channels, including zero,
and for graphs with no pair roots.  A zero-channel vector has its one empty
value; a graph with no pair roots has its one empty shared assignment.  No
dummy graph edge or common mixing variable is introduced in either boundary.

All enumerations and equality decisions are the explicit finite dependent
product constructions.  The unit-weight atom theorems identify the whole
prior, including its literal denominator, without evaluating its potentially
exponential concrete support.  The channel transpose is an explicit inverse
pair of functions, not a selected probabilistic coupling.

`model` supplies an actual SCM for any declared-input mechanism.  It is an
input-family realization, not the missing graph-specific countermodel: local
positive tables, matching observational laws and a causal gap still have to
be constructed and proved separately.
-/

variable {S : ObservedSignature}

/-- One pair root carries one Boolean value for each finite channel. -/
abbrev BitVector (channels : Nat) := Fin channels -> Bool

/-- The explicit Cartesian list; duplicate-freeness is proved rather than
enforced by selecting or deduplicating representatives. -/
def bitEnumeration (channels : Nat) : List (BitVector channels) :=
  FiniteProduct.enumeration channels (fun _ => Bool) (fun _ => [false, true])

/-- Every vector occurs, including the empty vector at zero channels. -/
theorem bitEnumeration_complete (channels : Nat) (bits : BitVector channels) :
    bits ∈ bitEnumeration channels :=
  FiniteProduct.enumeration_complete channels (fun _ => Bool) (fun _ => [false, true])
    (fun _ bit => by cases bit <;> simp) bits

/-- Every vector occurs once.  Only finite Boolean equality is used. -/
theorem bitEnumeration_nodup (channels : Nat) : (bitEnumeration channels).Nodup :=
  FiniteProduct.enumeration_nodup channels (fun _ => Bool) (fun _ => [false, true])
    (fun _ => inferInstance) (fun _ => by change ([false, true] : List Bool).Nodup; decide)

/-- A compact explicit index for a local channel-signal vector.  Encoding
and decoding are supplied by the complete repetition-free vector list;
there is no chosen row representative or inverse of a many-to-one encoder. -/
def bitWitness (channels : Nat) : FiniteWitness (BitVector channels) := by
  letI : DecidableEq (BitVector channels) :=
    FiniteProduct.assignmentDecidableEq channels (fun _ => Bool) (fun _ => inferInstance)
  exact FiniteWitness.ofList (bitEnumeration channels) (bitEnumeration_complete channels)
    (bitEnumeration_nodup channels)

/-- The actual normalized two-atom fair bit record. -/
def fairBit : FiniteProbRecord Bool where
  atoms := [(false, 1), (true, 1)]
  den := 2
  den_pos := by decide
  total_mass := rfl

/-- A root's channel coordinates are themselves genuinely independent. -/
def factor (channels : Nat) : FiniteProbRecord (BitVector channels) :=
  FiniteProduct.record channels (fun _ => Bool) (fun _ => fairBit)

/-- The factor's actual atoms are the complete unit-weight vector list. -/
theorem factor_atoms (channels : Nat) :
    (factor channels).atoms = (bitEnumeration channels).map (fun bits => (bits, 1)) :=
  FiniteProduct.record_atoms_eq_unit channels (fun _ => Bool) (fun _ => fairBit)
    (fun _ => [false, true]) (fun _ => rfl)

/-- Normalization retains the literal length of that vector list. -/
theorem factor_den (channels : Nat) : (factor channels).den = (bitEnumeration channels).length :=
  FiniteProduct.record_den_eq_length channels (fun _ => Bool) (fun _ => fairBit)
    (fun _ => [false, true]) (fun _ => rfl)

/-- Each real root-vector cell has literal numerator one.  This stronger
statement, not just positivity, permits the shared factors to disappear
from the likelihood numerator while their normalization remains explicit. -/
theorem factor_singleton_num (channels : Nat) (bits : BitVector channels) :
    letI : DecidableEq (BitVector channels) :=
      FiniteProduct.assignmentDecidableEq channels (fun _ => Bool) (fun _ => inferInstance)
    ((factor channels).probVal (FiniteProbRecord.singletonEvent bits)).num = 1 := by
  letI : DecidableEq (BitVector channels) :=
    FiniteProduct.assignmentDecidableEq channels (fun _ => Bool) (fun _ => inferInstance)
  change FiniteProbRecord.eventMass (factor channels).atoms (FiniteProbRecord.singletonEvent bits) = 1
  rw [factor_atoms]
  exact FiniteProbRecord.eventMass_unit_singleton _ (bitEnumeration_nodup channels) bits
    (bitEnumeration_complete channels bits)

private theorem unit_mass_positive {Ω : Type u} (values : List Ω) (value : Ω)
    (member : value ∈ values) (event : Event Ω) (selected : event value = true) :
    0 < FiniteProbRecord.eventMass (values.map (fun sample => (sample, 1))) event := by
  rw [FiniteProbRecord.eventMass_unit, count, List.countP_eq_length_filter]
  have occurs := List.mem_filter.mpr ⟨member, selected⟩
  cases filtered : values.filter event with
  | nil => rw [filtered] at occurs; cases occurs
  | cons head tail => simp only [List.length_cons]; omega

/-- Each complete channel vector has positive mass in the actual factor. -/
theorem factor_positive (channels : Nat) (bits : BitVector channels) :
    letI : DecidableEq (BitVector channels) :=
      FiniteProduct.assignmentDecidableEq channels (fun _ => Bool) (fun _ => inferInstance)
    (factor channels).EventPositive (FiniteProbRecord.singletonEvent bits) := by
  letI : DecidableEq (BitVector channels) :=
    FiniteProduct.assignmentDecidableEq channels (fun _ => Bool) (fun _ => inferInstance)
  change 0 < FiniteProbRecord.eventMass (factor channels).atoms (FiniteProbRecord.singletonEvent bits)
  rw [factor_atoms]
  exact unit_mass_positive _ bits (bitEnumeration_complete channels bits) _ (by
    simp only [FiniteProbRecord.singletonEvent, decide_true])

/-- Enlarge only each root's finite alphabet; keep the pair-root incidence
literally.  The channel count cannot change the projected graph. -/
def extension (G : ObservedGraph S) (channels : Nat) : LatentExtension S where
  count := pairRootCount G
  Value := fun _ => BitVector channels
  valueEnumeration := fun _ => bitEnumeration channels
  value_complete := fun _ => bitEnumeration_complete channels
  valueDecidableEq := fun _ =>
    FiniteProduct.assignmentDecidableEq channels (fun _ => Bool) (fun _ => inferInstance)
  incident := pairRootIncident G

/-- No channel coordinate creates a third observed child at a pair root. -/
theorem extension_canonical (G : ObservedGraph S) (channels : Nat) :
    (extension G channels).CanonicalSemiMarkovian :=
  pairRootExtension_canonical G

/-- Hiding these same pair roots recovers the original bidirected graph. -/
theorem extension_projected (G : ObservedGraph S) (channels : Nat) (left right : Fin S.count) :
    (extension G channels).projectedBidirected left right = G.bidirected left right :=
  pairRootExtension_projected G left right

/-- The actual independent prior groups coordinates by the roots declared
in the SCM, not by a globally shared channel source. -/
def prior (G : ObservedGraph S) (channels : Nat) : FiniteProbRecord (extension G channels).Assignment :=
  FiniteProduct.record (pairRootCount G) (fun _ => BitVector channels) (fun _ => factor channels)

/-- The root-major list enumerates every actual shared assignment. -/
def enumeration (G : ObservedGraph S) (channels : Nat) : List (extension G channels).Assignment :=
  FiniteProduct.enumeration (pairRootCount G) (fun _ => BitVector channels) (fun _ => bitEnumeration channels)

/-- The actual source alphabet is completely covered by the root-major list. -/
theorem enumeration_complete (G : ObservedGraph S) (channels : Nat)
    (assignment : (extension G channels).Assignment) : assignment ∈ enumeration G channels :=
  FiniteProduct.enumeration_complete (pairRootCount G) (fun _ => BitVector channels)
    (fun _ => bitEnumeration channels) (fun _ => bitEnumeration_complete channels) assignment

/-- Each actual shared assignment occurs once in this product presentation. -/
theorem enumeration_nodup (G : ObservedGraph S) (channels : Nat) : (enumeration G channels).Nodup :=
  FiniteProduct.enumeration_nodup (pairRootCount G) (fun _ => BitVector channels)
    (fun _ => bitEnumeration channels)
    (fun _ => FiniteProduct.assignmentDecidableEq channels (fun _ => Bool) (fun _ => inferInstance))
    (fun _ => bitEnumeration_nodup channels)

/-- Whole-prior weights are the actual unit weights, not just a list of
possible labels with an unspecified or correlated probability assignment. -/
theorem prior_atoms (G : ObservedGraph S) (channels : Nat) :
    (prior G channels).atoms = (enumeration G channels).map (fun assignment => (assignment, 1)) :=
  FiniteProduct.record_atoms_eq_unit (pairRootCount G) (fun _ => BitVector channels)
    (fun _ => factor channels) (fun _ => bitEnumeration channels) (fun _ => factor_atoms channels)

/-- The full prior's literal denominator counts exactly these unit atoms. -/
theorem prior_den (G : ObservedGraph S) (channels : Nat) :
    (prior G channels).den = (enumeration G channels).length :=
  FiniteProduct.record_den_eq_length (pairRootCount G) (fun _ => BitVector channels)
    (fun _ => factor channels) (fun _ => bitEnumeration channels) (fun _ => factor_atoms channels)

/-- Every complete root-major assignment has positive mass, including the
one empty assignment when the graph has no pair roots. -/
theorem prior_positive (G : ObservedGraph S) (channels : Nat) (assignment : (extension G channels).Assignment) :
    (prior G channels).EventPositive (FiniteProbRecord.singletonEvent assignment) := by
  change 0 < FiniteProbRecord.eventMass (prior G channels).atoms (FiniteProbRecord.singletonEvent assignment)
  rw [prior_atoms]
  exact unit_mass_positive _ assignment (enumeration_complete G channels assignment) _ (by
    simp only [FiniteProbRecord.singletonEvent, decide_true])

/-- Read the same finite matrix by channel.  This changes grouping only;
each bit remains the coordinate of its original actual pair-root source. -/
def channelBits (G : ObservedGraph S) (channels : Nat) (assignment : (extension G channels).Assignment) :
    Fin channels -> Fin (pairRootCount G) -> Bool :=
  fun channel root => assignment root channel

/-- The displayed inverse restores the root-major source grouping. -/
def fromChannelBits (G : ObservedGraph S) (channels : Nat)
    (blocks : Fin channels -> Fin (pairRootCount G) -> Bool) : (extension G channels).Assignment :=
  fun root channel => blocks channel root

/-- Reading by channel and back restores every original root vector. -/
theorem fromChannelBits_channelBits (G : ObservedGraph S) (channels : Nat) (assignment : (extension G channels).Assignment) :
    fromChannelBits G channels (channelBits G channels assignment) = assignment := rfl

/-- The reverse transpose likewise restores every full channel block. -/
theorem channelBits_fromChannelBits (G : ObservedGraph S) (channels : Nat)
    (blocks : Fin channels -> Fin (pairRootCount G) -> Bool) :
    channelBits G channels (fromChannelBits G channels blocks) = blocks := rfl

/-- Rectangular independence belongs to this actual product prior. -/
theorem prior_product_law (G : ObservedGraph S) (channels : Nat)
    (events : (root : Fin (extension G channels).count) -> (extension G channels).Value root -> Bool) :
    QProb.Equiv ((prior G channels).probVal ((extension G channels).rectangularEvent events))
      (FiniteProduct.qProduct (pairRootCount G) (fun root => (factor channels).probVal (events root))) :=
  FiniteProduct.record_rectangular_probVal (pairRootCount G) (fun _ => BitVector channels)
    (fun _ => factor channels) events

/-- Actual SCM input-family realization.  Each supplied mechanism receives
only declared directed parents and incident pair-root channel vectors. -/
def model (G : ObservedGraph S) (channels : Nat)
    (mechanism : (child : Fin S.count) -> S.ParentValues child -> (extension G channels).Inputs child -> S.Value child) :
    FiniteLatentSCM S where
  latent := extension G channels
  factor := fun _ => factor channels
  prior := prior G channels
  product_law := prior_product_law G channels
  mechanism := mechanism

/-- Source realization preserves canonical semi-Markovian incidence for
every declared-input mechanism, irrespective of how its rows respond. -/
theorem model_canonical (G : ObservedGraph S) (channels : Nat)
    (mechanism : (child : Fin S.count) -> S.ParentValues child -> (extension G channels).Inputs child -> S.Value child) :
    (model G channels mechanism).IsCanonicalSemiMarkovian := extension_canonical G channels

/-- The SCM's hidden projection recovers every original bidirected edge. -/
theorem model_projected (G : ObservedGraph S) (channels : Nat)
    (mechanism : (child : Fin S.count) -> S.ParentValues child -> (extension G channels).Inputs child -> S.Value child)
    (left right : Fin S.count) :
    (model G channels mechanism).observedGraph.bidirected left right = G.bidirected left right :=
  extension_projected G channels left right

end PairRootChannels
end Causality
end Thesis
