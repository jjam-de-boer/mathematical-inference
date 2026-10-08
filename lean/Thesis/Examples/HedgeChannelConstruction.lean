import Thesis.CausalTransport.HedgeChannelCharacters
import Thesis.CausalTransport.HedgeChannelOrthogonality
import Thesis.Probability.BooleanChannelTable

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeChannelConstruction

open Probability

/-!
# Small checks for the independent-channel construction ingredients

A two-node bow checks that a selected outer bit is transferred to a small
child through the actual typed parent map.  The small character deliberately
reads that outer parent, rather than using the original restricted forest
signal.  The general factorization theorem must retain this arbitrary local
signal.  A proper one-node incidence character is also checked as fair under
the actual normalized pair-bit record.

The table checks use three channels, including a zero amplitude and two
coincident centres.  Moving the centre bits changes the row probabilities
but not their common chosen denominator or their full support.

These are boundary regressions of general lemmas, not a restricted substitute
for the universal hedge countermodel.  Neither an exhaustive alternative-hedge
scan nor a private response-function enumeration is evaluated here.
-/

def signature : ObservedSignature where
  count := 2
  Value := fun _ => Bool
  valueEnumeration := fun _ => [false, true]
  value_complete := by intro _ value; cases value <;> simp
  value_nodup := fun _ => by decide
  defaultValue := fun _ => false
  valueDecidableEq := fun _ => inferInstance
  directed := fun parent child => decide (parent.val = 0 ∧ child.val = 1)
  directed_earlier := by intro parent child selected; have edge := of_decide_eq_true selected; omega

def graph : ObservedGraph signature where
  bidirected := fun left right => decide (left ≠ right)
  bidirected_symmetric := by intro left right selected; simpa only [ne_comm] using selected
  bidirected_irreflexive := fun _ => by simp

def actionNode : Fin signature.count := ⟨0, by decide⟩
def outcomeNode : Fin signature.count := ⟨1, by decide⟩

def query : JointKernelQuery signature where
  outcome := NodeSet.singleton outcomeNode
  action := NodeSet.singleton actionNode
  action_outcome_disjoint := NodeSet.disjoint_singletons_of_ne (by decide)

def selection : HedgeSelection signature where
  large := NodeSet.full
  small := NodeSet.singleton outcomeNode
  child := fun parent => if parent = actionNode then some outcomeNode else none

def witness : HedgeWitness graph query :=
  hedgeWitness_of_sets graph query selection (by decide +kernel)

def rich : ObservedSignature.ValueRich signature where
  first := fun _ => false
  second := fun _ => true
  first_enumerated := fun _ => by change false ∈ [false, true]; decide
  second_enumerated := fun _ => by change true ∈ [false, true]; decide
  different := fun _ => Bool.false_ne_true

/-- A local signal is allowed to read an actual outer directed parent.
It is not required to coincide with the old small-forest parent parity. -/
def smallSignal (child : Fin signature.count) (parents : signature.ParentValues child) : Bool :=
  if edge : signature.directed actionNode child = true then parents actionNode edge else false

def backgroundSignal (_child : Fin signature.count) (_parents : signature.ParentValues _child) : Bool := true

/-- Character factorization holds at every full sample, including the
typed parent signal that the old nested carrier deliberately ignored. -/
theorem outer_parent_character (sample : signature.Assignment) :
    hedgeNodeXor witness.large (fun child => Bool.xor (hedgeIsSecond rich child (sample child))
      (witness.channelParentSignal rich (NodeSet.singleton actionNode) smallSignal backgroundSignal child
        (fun parent _edge => sample parent))) =
      Bool.xor
        (hedgeNodeXor witness.small (fun child => Bool.xor (hedgeIsSecond rich child (sample child))
          (smallSignal child (fun parent _edge => sample parent))))
        (hedgeNodeXor (NodeSet.singleton actionNode) (fun child => Bool.xor (hedgeIsSecond rich child (sample child))
          (backgroundSignal child (fun parent _edge => sample parent)))) :=
  witness.channelCharacter_factorization rich _ (by
    intro node selected
    have same := (NodeSet.singleton_eq_true_iff actionNode node).mp selected
    subst node
    decide +kernel) smallSignal backgroundSignal sample

/-- Proper-subset cancellation uses the general incidence theorem rather
than evaluating a large channel enumeration or assuming a uniform parity. -/
theorem proper_character_fair (phase : Bool) :
    QProb.Equiv ((hedgeChannelPairBitRecord graph).probVal (fun bits => Bool.xor phase
      (hedgeChannelIncidenceParity graph NodeSet.full (NodeSet.singleton actionNode) bits))) ⟨1, 2, by decide⟩ :=
  witness.large_forest.component.channelParity_probVal_half graph _ _ (by intro node _selected; rfl)
    outcomeNode (by decide +kernel) (by decide +kernel) actionNode (by decide +kernel) phase

private def amplitudes (channel : Fin 3) : Nat := channel.val

def table : BooleanChannelTable (Fin 3) :=
  BooleanChannelTable.ofCapacity (List.finRange 3) amplitudes 8 (by decide +kernel)

private def allTrue (_channel : Fin 3) : Bool := true
private def splitCentres (channel : Fin 3) : Bool := decide (channel.val = 2)

/-- Zero-amplitude and coincident channels retain full support at every
choice of centres.  Positivity belongs to the actual normalized records. -/
theorem rows_positive (signals : Fin 3 -> Bool) (value : Bool) :
    (table.record signals).EventPositive (FiniteProbRecord.singletonEvent value) :=
  table.record_positive signals value

/-- Local centre changes do not change the denominator at fixed capacity. -/
theorem common_denominator (signals : Fin 3 -> Bool) : (table.record signals).den = 16 := by
  rw [table.record_den]
  rfl

/-- Repeated centres accumulate both amplitudes.  Separating one centre
changes the probabilities, with the very same chosen row denominator. -/
theorem literal_cells :
    QProb.Equiv ((table.record allTrue).probVal (FiniteProbRecord.singletonEvent true)) ⟨11, 16, by decide⟩ ∧
    QProb.Equiv ((table.record splitCentres).probVal (FiniteProbRecord.singletonEvent true)) ⟨9, 16, by decide⟩ := by
  decide +kernel

end HedgeChannelConstruction
end Examples
end Causality
end Thesis
