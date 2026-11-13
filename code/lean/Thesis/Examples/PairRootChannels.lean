import Thesis.CausalTransport.HedgeChannelPairRoot

namespace Thesis
namespace Causality
namespace Examples
namespace PairRootChannels

open Probability

/-!
# Small whole-prior checks for actual pair-root channel vectors

A three-node bidirected chain has two different pair roots.  Two channels
therefore give a four-bit matrix, grouped into two independently sampled
root vectors.  The mixed event below compares opposite corners of that
matrix; it is not a rectangle in either grouping.  Its exact probability
checks the all-event transpose bridge rather than only marginal fairness.

Only the sixteen shared matrices are evaluated by the numerical regression.
No observed SCM execution, private response space or exhaustive graph search
is unfolded.  Separate symbolic checks cover zero channels and zero roots.
-/

def signature : ObservedSignature where
  count := 3
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := fun _ => by decide
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ selected; cases selected

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left.val + 1 = right.val) || decide (right.val + 1 = left.val)
  bidirected_symmetric := by intro left right selected; simpa only [Bool.or_comm] using selected
  bidirected_irreflexive := by
    intro node
    have different : node.val + 1 ≠ node.val := by omega
    simp only [different, decide_false, Bool.false_or]

private def firstRoot : Fin (pairRootCount graph) := ⟨0, by decide +kernel⟩
private def secondRoot : Fin (pairRootCount graph) := ⟨1, by decide +kernel⟩

private def mixedEvent (assignment : (Causality.PairRootChannels.extension graph 2).Assignment) : Bool :=
  Bool.xor (assignment firstRoot 0) (assignment secondRoot 1) &&
    Bool.xor (assignment firstRoot 1) (assignment secondRoot 0)

/-- The actual pair-root product gives probability one quarter to the
two simultaneous cross-corner parity constraints. -/
theorem mixed_event_probability :
    QProb.Equiv ((Causality.PairRootChannels.prior graph 2).probVal mixedEvent) ⟨1, 4, by decide⟩ := by
  decide +kernel

/-- The block presentation agrees on this nonrectangular event through the
general whole-prior theorem, retaining the displayed inverse transpose. -/
theorem mixed_event_transpose :
    QProb.Equiv ((hedgeChannelBlocksRecord graph 2).probVal
      (fun blocks => mixedEvent (Causality.PairRootChannels.fromChannelBits graph 2 blocks))) ⟨1, 4, by decide⟩ := by
  have transported := Causality.PairRootChannels.prior_probVal_channelBits graph 2
    (fun blocks => mixedEvent (Causality.PairRootChannels.fromChannelBits graph 2 blocks))
  exact QProb.equiv_trans (QProb.equiv_symm transported) mixed_event_probability

/-- Empty channel vectors do not add a latent choice at either root. -/
theorem zero_channels_denominator : (Causality.PairRootChannels.prior graph 0).den = 1 := by
  decide +kernel

def isolatedGraph : ObservedGraph signature where
  bidirected := fun _ _ => false
  bidirected_symmetric := by intro _ _ selected; cases selected
  bidirected_irreflexive := fun _ => rfl

/-- With no pair roots the actual shared prior has one empty assignment,
even for an arbitrary symbolic number of channels.  No channel enumeration
is evaluated to establish this boundary. -/
theorem zero_roots_denominator (channels : Nat) :
    (Causality.PairRootChannels.prior isolatedGraph channels).den = 1 := by
  change 1 = 1
  rfl

/-- Reindexing still preserves every event when one matrix dimension is
empty; the theorem does not require choosing a root or a channel. -/
theorem zero_roots_transpose (channels : Nat)
    (event : Event (Fin channels -> Fin (pairRootCount isolatedGraph) -> Bool)) :
    QProb.Equiv ((Causality.PairRootChannels.prior isolatedGraph channels).probVal
      (fun assignment => event (Causality.PairRootChannels.channelBits isolatedGraph channels assignment)))
      ((hedgeChannelBlocksRecord isolatedGraph channels).probVal event) :=
  Causality.PairRootChannels.prior_probVal_channelBits isolatedGraph channels event

end PairRootChannels
end Examples
end Causality
end Thesis
