import Thesis.CausalTransport.HedgeChannelPairRoot
import Thesis.Causality.BinaryEncoding
import Thesis.Causality.LatentRationalCPT
import Thesis.Probability.BooleanChannelExpansion

namespace Thesis
namespace Causality
namespace HedgeChannelTable

open Probability

/-!
# Actual positive binary tables with graph-compatible channel inputs

The independent channels are now installed at the original pair roots.
Each local signal below receives only declared directed parents and incident
root vectors.  `cpt` turns positive `BooleanChannelTable` rows into the actual
finite rational table SCM, using one private response source per observed
node.  Those private sources have only one child, so both canonical incidence
and the entire projected bidirected graph are preserved exactly.

Row configurations enumerate only the finite vector of channel centre bits.
The typed parent/shared encoder can deliberately merge configurations with
the same centres.  Its lookup theorem follows from the explicit finite
vector encode/decode identity; no representative of an encoder fibre is
selected.  The semantic CPT theorems integrate the private response sources
symbolically rather than evaluating their potentially much larger support.

Strict observed positivity is proved using the explicit all-zero shared
assignment and the actual positive row records.  This is full Boolean support
for every original observed coordinate, not merely positive query evidence.
The general construction does not yet choose the two graph-specific signal
and amplitude families that have equal observational laws and a causal gap.
-/

variable {S : ObservedSignature.{0}}

/-- Local channel centres are functions only of the typed declared inputs.
The binary signature retains the original graph and observed node count. -/
abbrev Signals (G : ObservedGraph S) (channels : Nat) :=
  (child : Fin S.count) -> S.binary.ParentValues child ->
    (PairRootChannels.extension G.binary channels).Inputs child -> PairRootChannels.BitVector channels

/-- Positive channel rows in an actual finite latent rational CPT.  The
shared family is the original pair-root family with vector alphabets; row
configuration indices encode centre bits, not global latent assignments. -/
def cpt (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels) :
    FiniteLatentRationalCPT S.binary where
  shared := PairRootChannels.extension G.binary channels
  sharedFactor := fun _ => PairRootChannels.factor channels
  configCount := fun _ => (PairRootChannels.bitWitness channels).card
  encode := fun child parents inputs => (PairRootChannels.bitWitness channels).encode (signals child parents inputs)
  row := fun child configuration => (tables child).record ((PairRootChannels.bitWitness channels).decode configuration)

/-- Looking up a typed local configuration returns exactly its stated
positive channel row, even when different parent inputs share centre bits. -/
theorem cpt_row_encode (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (child : Fin S.count) (parents : S.binary.ParentValues child)
    (inputs : (PairRootChannels.extension G.binary channels).Inputs child) :
    (cpt G channels tables signals).row child ((cpt G channels tables signals).encode child parents inputs) =
      (tables child).record (signals child parents inputs) := by
  change (tables child).record ((PairRootChannels.bitWitness channels).decode
    ((PairRootChannels.bitWitness channels).encode (signals child parents inputs))) = _
  rw [(PairRootChannels.bitWitness channels).decode_encode]

/-- The functionalized object is an actual SCM with its independent shared
prefix and private response suffix, not a table-shaped external interface. -/
def model (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels) : ExactModel S.binary :=
  (cpt G channels tables signals).toSCM

/-- Both the canonical two-child bound and the exact projected graph hold
for the actual positive-row model, with no extra common mixing source. -/
theorem model_compatible (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels) :
    Compatible (model G channels tables signals) G.binary :=
  (cpt G channels tables signals).toSCM_compatible G.binary
    (PairRootChannels.extension_canonical G.binary channels)
    (PairRootChannels.extension_projected G.binary channels)

/-- Every complete observed Boolean assignment has positive probability.
The supporting shared assignment is the explicit zero vector at every root;
positive rows then support the full observed sample through the actual CPT
semantics.  No soundness theorem or chosen latent witness is used. -/
theorem model_positive (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels) :
    ObservationallyPositive (model G channels tables signals) := by
  apply (cpt G channels tables signals).toSCM_observationallyPositive_of_supportedShared
    (fun _root _channel => false)
  · intro root
    exact PairRootChannels.factor_positive channels (fun _ => false)
  · intro sample child
    rw [cpt_row_encode]
    exact (tables child).record_positive _ (sample child)

/-- The natural row numerator used by the actual CPT is exactly the finite
capacity-plus-character expression.  This links local character algebra to
the normalized row weights before any whole-model comparison is claimed. -/
theorem cpt_row_num_cast (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (child : Fin S.count) (parents : S.binary.ParentValues child)
    (inputs : (PairRootChannels.extension G.binary channels).Inputs child) (value : Bool) :
    ((((cpt G channels tables signals).row child ((cpt G channels tables signals).encode child parents inputs)).probVal
      (FiniteProbRecord.singletonEvent value)).num : Int) =
      (tables child).cellNumerator (signals child parents inputs) value := by
  rw [cpt_row_encode]
  exact (tables child).record_num_cast _ value

/-- The actual integrated private-response factor is the stated channel cell
at a free row and the actual forced-value indicator at an intervened row.
This identifies the factor already used by the CPT likelihood theorem. -/
theorem privateFactor_eq_cellUnder (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (shared : (PairRootChannels.extension G.binary channels).Assignment)
    (sample : S.binary.Assignment) (child : Fin S.count) :
    (cpt G channels tables signals).sliceFactors target shared sample
      ((cpt G channels tables signals).privateRoot child) =
      (tables child).cellUnder (signals child (fun parent _edge => sample parent)
        (fun root _incident => shared root)) (target child) (sample child) := by
  rw [FiniteLatentRationalCPT.sliceFactors_privateRoot]
  unfold FiniteLatentRationalCPT.rowValueUnder
  cases selected : target child with
  | none =>
      simp only [BooleanChannelTable.cellUnder]
      rw [cpt_row_encode]
      rfl
  | some fixed => rfl

/-- Complete expansion of the actual integrated private-row product for a
fixed shared assignment.  Every hard intervention and cross-row interaction
is retained.  The shared-prior integration and graph-specific coefficient
matching are still needed to compare whole observational laws. -/
theorem privateProduct_num_expansion (G : ObservedGraph S) (channels : Nat)
    (tables : Fin S.count -> BooleanChannelTable (Fin channels)) (signals : Signals G channels)
    (target : Fin S.count -> Option Bool) (shared : (PairRootChannels.extension G.binary channels).Assignment)
    (sample : S.binary.Assignment) :
    ((FiniteProduct.qProduct S.count (fun child => (cpt G channels tables signals).sliceFactors target shared sample
      ((cpt G channels tables signals).privateRoot child))).num : Int) =
      ((FiniteProduct.enumeration S.count (fun _ => Option (Fin channels))
        (fun child => (tables child).expansionChoicesUnder (target child))).map fun assignment =>
          FiniteProduct.iProduct S.count (fun child => (tables child).expansionTermUnder
            (signals child (fun parent _edge => sample parent) (fun root _incident => shared root))
            (target child) (sample child) (assignment child))).sum := by
  have factors : (fun child => (cpt G channels tables signals).sliceFactors target shared sample
      ((cpt G channels tables signals).privateRoot child)) =
      (fun child => (tables child).cellUnder
        (signals child (fun parent _edge => sample parent) (fun root _incident => shared root))
        (target child) (sample child)) :=
    funext (fun child => privateFactor_eq_cellUnder G channels tables signals target shared sample child)
  have products := congrArg (fun values : Fin S.count -> QProb => ((FiniteProduct.qProduct S.count values).num : Int)) factors
  exact products.trans (BooleanChannelTable.product_num_expansion S.count (fun _ => Fin channels) tables
    (fun child => signals child (fun parent _edge => sample parent) (fun root _incident => shared root)) target sample)

end HedgeChannelTable
end Causality
end Thesis
