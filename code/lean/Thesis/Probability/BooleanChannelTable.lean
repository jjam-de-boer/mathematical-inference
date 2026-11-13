import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability

/-!
# Positive Boolean rows carrying finitely many local channel terms

A local table may contain several independent hidden-channel characters.
Their signed-looking biases need not introduce negative probability weights:
put one positive baseline atom at each Boolean value, and put twice each
channel amplitude at that channel's supplied output bit.  The result is an
actual normalized finite record, with positive mass at both values.

The denominator depends only on the baseline and total amplitudes, never
on the parent-dependent or hidden-input-dependent signal bits.  Thus the
same channel data supplies a legitimate table row at every configuration.
`ofCapacity` permits different amplitude families to use one chosen capacity,
provided that capacity strictly exceeds each finite amplitude sum.

The cell-balance theorem identifies the two nonnegative parts of the exact
deviation from a fair Boolean row.  These are algebraic channel contributions,
not extra common latent sources or global mixture switches.  Independence,
graph incidence and observational cancellation of a family of SCM tables
remain separate obligations; no countermodel existence is asserted here.
-/

/-- Explicit local channel amplitudes and a strictly positive baseline.
Every list occurrence is one summand; duplicate channel labels accumulate
their amplitudes rather than being silently deduplicated. -/
structure BooleanChannelTable (Channel : Type u) where
  channels : List Channel
  amplitude : Channel -> Nat
  baseline : Nat
  baselinePositive : 0 < baseline

namespace BooleanChannelTable

open FiniteProbRecord

variable {Channel : Type u}

/-- One half of the total row mass.  Signals do not change this capacity. -/
def capacity (table : BooleanChannelTable Channel) : Nat :=
  table.baseline + (table.channels.map table.amplitude).sum

theorem capacity_positive (table : BooleanChannelTable Channel) : 0 < table.capacity :=
  Nat.lt_of_lt_of_le table.baselinePositive (Nat.le_add_right _ _)

/-- Build a channel family at an explicit common capacity.  The leftover
baseline is positive by the supplied finite natural-number inequality. -/
def ofCapacity (channels : List Channel) (amplitude : Channel -> Nat) (capacity : Nat)
    (room : (channels.map amplitude).sum < capacity) : BooleanChannelTable Channel where
  channels := channels
  amplitude := amplitude
  baseline := capacity - (channels.map amplitude).sum
  baselinePositive := Nat.sub_pos_iff_lt.mpr room

/-- The chosen capacity is retained exactly, so comparing different
amplitude families need not alter the row denominator. -/
theorem ofCapacity_capacity (channels : List Channel) (amplitude : Channel -> Nat) (capacity : Nat)
    (room : (channels.map amplitude).sum < capacity) :
    (ofCapacity channels amplitude capacity room).capacity = capacity :=
  Nat.sub_add_cancel (Nat.le_of_lt room)

/-- Raw channel atoms before the factor of two used by the normalized row.
Signals can be instantiated by arbitrary legal parent and hidden inputs. -/
def centreAtoms (table : BooleanChannelTable Channel) (signals : Channel -> Bool) : List (Bool × Nat) :=
  table.channels.map fun channel => (signals channel, table.amplitude channel)

private theorem centreAtoms_total (table : BooleanChannelTable Channel) (signals : Channel -> Bool) :
    totalMass (table.centreAtoms signals) = (table.channels.map table.amplitude).sum := by
  unfold centreAtoms
  induction table.channels with
  | nil => rfl
  | cons channel rest inductionHypothesis =>
      simp only [List.map_cons, totalMass, List.sum_cons]
      rw [inductionHypothesis]

/-- A finite normalized row on the actual Boolean output values.  The
positive baseline remains present even when every channel favors one value. -/
def record (table : BooleanChannelTable Channel) (signals : Channel -> Bool) : FiniteProbRecord Bool where
  atoms := [(false, table.baseline), (true, table.baseline)] ++
    (table.centreAtoms signals).map (fun atom => (atom.1, 2 * atom.2))
  den := 2 * table.capacity
  den_pos := Nat.mul_pos (by decide) table.capacity_positive
  total_mass := by
    rw [totalMass_append]
    have scaled : totalMass ((table.centreAtoms signals).map (fun atom => (atom.1, 2 * atom.2))) =
        2 * totalMass (table.centreAtoms signals) :=
      totalMass_map_weight (table.centreAtoms signals) id 2
    rw [scaled, centreAtoms_total]
    simp only [totalMass, Nat.add_zero, capacity, Nat.mul_add]
    omega

/-- All configurations share this literal denominator, regardless of their
signal values.  This is stronger than merely equivalent normalization. -/
theorem record_den (table : BooleanChannelTable Channel) (signals : Channel -> Bool) :
    (table.record signals).den = 2 * table.capacity := rfl

/-- Each singleton mass is its baseline plus twice the matching channel
amplitudes.  Repeated centres contribute through ordinary event-mass sums. -/
theorem record_singleton_mass (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) :
    eventMass (table.record signals).atoms (singletonEvent value) =
      table.baseline + 2 * eventMass (table.centreAtoms signals) (singletonEvent value) := by
  rw [record, eventMass_append, eventMass_scale]
  cases value <;> simp [eventMass, singletonEvent]

/-- Full Boolean support follows from the actual row atoms and positive
baseline; it is not a positivity premise about the character amplitudes. -/
theorem record_positive (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) :
    (table.record signals).EventPositive (singletonEvent value) := by
  unfold EventPositive
  rw [table.record_singleton_mass signals value]
  exact Nat.lt_of_lt_of_le table.baselinePositive (Nat.le_add_right _ _)

private theorem boolean_mass_partition (atoms : List (Bool × Nat)) (value : Bool) :
    eventMass atoms (singletonEvent value) + eventMass atoms (singletonEvent (!value)) = totalMass atoms := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨centre, amplitude⟩
      cases centre <;> cases value <;>
        simpa [eventMass, singletonEvent, totalMass, Nat.add_assoc, Nat.add_left_comm] using
          congrArg (fun mass => amplitude + mass) inductionHypothesis

/-- Every channel amplitude occurs on exactly one side of a Boolean
singleton.  The partition is constructive even with zero amplitudes. -/
theorem centre_mass_partition (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) :
    eventMass (table.centreAtoms signals) (singletonEvent value) +
      eventMass (table.centreAtoms signals) (singletonEvent (!value)) =
        (table.channels.map table.amplitude).sum :=
  (boolean_mass_partition _ value).trans (centreAtoms_total table signals)

/-- Matching channels are the positive part of the fair-row deviation. -/
def positiveCell (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) : QProb :=
  ⟨eventMass (table.centreAtoms signals) (singletonEvent value), 2 * table.capacity,
    Nat.mul_pos (by decide) table.capacity_positive⟩

/-- Opposite channels are its negative part.  This remains a nonnegative
raw cell family, not a signed probability distribution. -/
def negativeCell (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) : QProb :=
  ⟨eventMass (table.centreAtoms signals) (singletonEvent (!value)), 2 * table.capacity,
    Nat.mul_pos (by decide) table.capacity_positive⟩

/-- The fair reference cell written on the exact same row denominator. -/
def uniformCell (table : BooleanChannelTable Channel) : QProb :=
  ⟨table.capacity, 2 * table.capacity, Nat.mul_pos (by decide) table.capacity_positive⟩

theorem uniformCell_half (table : BooleanChannelTable Channel) :
    QProb.Equiv table.uniformCell ⟨1, 2, by decide⟩ := by
  simp only [uniformCell, QProb.Equiv, Nat.one_mul, Nat.mul_comm]

/-- Exact two-sided deviation from a fair row, using only natural masses.
The fair part and every channel contribution retain the same denominator;
no positivity assumption or division by a character amplitude is needed. -/
theorem record_cell_balance (table : BooleanChannelTable Channel) (signals : Channel -> Bool) (value : Bool) :
    QProb.Equiv
      (QProb.add ((table.record signals).probVal (singletonEvent value)) (table.negativeCell signals value))
      (QProb.add table.uniformCell (table.positiveCell signals value)) := by
  let den := 2 * table.capacity
  have positive : 0 < den := Nat.mul_pos (by decide) table.capacity_positive
  let matchingMass := eventMass (table.centreAtoms signals) (singletonEvent value)
  let opposites := eventMass (table.centreAtoms signals) (singletonEvent (!value))
  have split : matchingMass + opposites = (table.channels.map table.amplitude).sum :=
    table.centre_mass_partition signals value
  have numerator : table.baseline + 2 * matchingMass + opposites = table.capacity + matchingMass := by
    unfold capacity
    omega
  have mass := table.record_singleton_mass signals value
  change QProb.Equiv
    (QProb.add ⟨eventMass (table.record signals).atoms (singletonEvent value), den, positive⟩
      ⟨opposites, den, positive⟩)
    (QProb.add ⟨table.capacity, den, positive⟩ ⟨matchingMass, den, positive⟩)
  rw [mass]
  exact QProb.equiv_trans (QProb.add_mk_same_den den positive _ _)
    (QProb.equiv_trans (by rw [numerator]; exact QProb.equiv_refl _)
      (QProb.equiv_symm (QProb.add_mk_same_den den positive _ _)))

end BooleanChannelTable
end Probability
end Thesis
