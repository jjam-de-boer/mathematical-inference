import Thesis.Probability.BooleanChannelExpansion
import Thesis.Probability.Construction

namespace Thesis
namespace Probability
namespace BooleanChannelTable

/-!
# Reserving a latent coordinate without changing a positive row

An independent environment bit may be needed by a local signal even when it
is not one of that row's character channels.  Enlarging the channel alphabet
must not accidentally add a new bias, change a capacity, or duplicate any
listed summand.  `reserveChannel` therefore includes each old label once in
the initial block and leaves the new terminal label out of the channel list.

The resulting row is literally the old finite probability record evaluated
on the initial centre bits.  In particular, its numerator, denominator and
positive baseline are unchanged.  This is a row-level bookkeeping identity,
not permission to treat a correlated hidden bit as independent: the actual
pair-root prior and its environment decomposition are proved separately.

The constructive `FiniteProduct.extend` is used deliberately.  Its explicit
finite-index reductions do not require an inverse chosen from a proposition.
-/

/-- Include every old character label in the initial block.  The extra
terminal coordinate has amplitude zero and is never listed as a summand. -/
def reserveChannel {channels : Nat} (table : BooleanChannelTable (Fin channels)) :
    BooleanChannelTable (Fin (channels + 1)) where
  channels := table.channels.map Fin.castSucc
  amplitude := FiniteProduct.extend 0 table.amplitude
  baseline := table.baseline
  baselinePositive := table.baselinePositive

/-- The literal half-mass is unchanged, including repeated old labels and
the zero-channel boundary.  No deduplication or amplitude rescaling occurs. -/
theorem reserveChannel_capacity {channels : Nat} (table : BooleanChannelTable (Fin channels)) :
    table.reserveChannel.capacity = table.capacity := by
  simp only [capacity, reserveChannel, List.map_map, Function.comp_def,
    FiniteProduct.extend_castSucc]

/-- Every old centre atom is retained once with exactly its old amplitude.
The reserved terminal centre is irrelevant, whatever Boolean value it has. -/
theorem reserveChannel_centreAtoms {channels : Nat}
    (table : BooleanChannelTable (Fin channels)) (signals : Fin (channels + 1) -> Bool) :
    table.reserveChannel.centreAtoms signals = table.centreAtoms (fun channel => signals channel.castSucc) := by
  simp only [centreAtoms, reserveChannel, List.map_map, Function.comp_def,
    FiniteProduct.extend_castSucc]

/-- Reserving the independent-input slot changes neither the actual atom
list nor its actual denominator; this is record equality, not merely equality
of normalized probabilities at one selected output value. -/
theorem reserveChannel_record {channels : Nat}
    (table : BooleanChannelTable (Fin channels)) (signals : Fin (channels + 1) -> Bool) :
    table.reserveChannel.record signals = table.record (fun channel => signals channel.castSucc) := by
  simp only [record, reserveChannel_centreAtoms, reserveChannel_capacity]
  rfl

/-- The same literal row identity holds under every hard intervention.
Forced consistency indicators, including zero cells, are not divided out. -/
theorem reserveChannel_cellUnder {channels : Nat}
    (table : BooleanChannelTable (Fin channels)) (signals : Fin (channels + 1) -> Bool)
    (target : Option Bool) (value : Bool) :
    table.reserveChannel.cellUnder signals target value =
      table.cellUnder (fun channel => signals channel.castSucc) target value := by
  cases target with
  | none => simp only [cellUnder, reserveChannel_record]
  | some fixed => rfl

end BooleanChannelTable
end Probability
end Thesis
