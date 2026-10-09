import Thesis.Probability.FiniteBooleanCharacter

namespace Thesis
namespace Probability
namespace FiniteProduct

/-!
# Constructive cancellation by a Boolean assignment translation

An XOR translation flips an explicitly supplied set of coordinates and is
its own inverse.  If a Boolean event ignores those flips, translation
permutes its actual filtered assignment enumeration.  A complete integer
integrand which changes sign under that translation consequently sums to
zero on the event.  Both the filtered support and all its occurrences are
retained; this is not a replacement probability law or a single-cell argument.

The theorem accepts any complete nonredundant Boolean assignment enumeration,
including the observed signature's actual list.  It does not enumerate a
concrete cube during elaboration, assume a linear character, or choose a
translation from a propositional existence statement.  The caller supplies
the direction as data and proves preservation of the event and reversal of
the actual weighted integrand.  Conditional hedge denominators use this
stronger statement to retain forced-row indicators and complete prior mass.
-/

/-- Flipping the same supplied coordinate direction twice recovers the
whole assignment.  This includes the empty direction and empty signature. -/
theorem xorAssignment_involutive (n : Nat) (direction sample : Fin n -> Bool) :
    xorAssignment n (xorAssignment n sample direction) direction = sample := by
  funext index
  unfold xorAssignment
  cases sample index <;> cases direction index <;> rfl

/-- Exact cancellation on an invariant Boolean event of the actual
supplied full assignment enumeration.  Sign reversal is required at every
selected cell, including cells whose integrand is already zero. -/
theorem filtered_sum_zero_of_xor (n : Nat) (values : List (Fin n -> Bool))
    (nodup : values.Nodup) (complete : forall sample, sample ∈ values)
    (direction : Fin n -> Bool) (event : (Fin n -> Bool) -> Bool)
    (preserved : forall sample, event (xorAssignment n sample direction) = event sample)
    (term : (Fin n -> Bool) -> Int)
    (opposite : forall sample, event sample = true ->
      term (xorAssignment n sample direction) = -(term sample)) :
    ((values.filter event).map term).sum = 0 := by
  letI : DecidableEq (Fin n -> Bool) := assignmentDecidableEq n (fun _ => Bool) (fun _ => inferInstance)
  apply FiniteSupportedSum.sum_zero_of_involution (values.filter event)
    (List.Pairwise.filter event nodup) (fun sample => xorAssignment n sample direction)
    (xorAssignment_involutive n direction)
  · intro sample listed
    exact List.mem_filter.mpr ⟨complete _, (preserved sample).trans (List.mem_filter.mp listed).2⟩
  · intro sample listed
    exact opposite sample (List.mem_filter.mp listed).2

end FiniteProduct
end Probability
end Thesis
