import Thesis.Probability.FiniteRecord

namespace Thesis
namespace Probability
namespace FiniteProbRecord

/-!
# Exact overlap accounting for finite Boolean events

The two event masses double-count their intersection.  Keeping that
intersection on the opposite side of an equality avoids truncated natural
subtraction and requires no positivity of either event.  Repeated atom
labels and zero weights are retained by the same finite-list calculation.

The consequent exposure bound applies whenever both observed events imply
one target event.  Its causal applications still have to prove those unit
implications and identify the intersection with an actual response cell.
-/

theorem eventMass_union_add_inter (atoms : List (Ω × Nat)) (left right : Event Ω) :
    eventMass atoms (union left right) + eventMass atoms (inter left right) =
      eventMass atoms left + eventMass atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      rcases atom with ⟨value, weight⟩
      cases atLeft : left value <;> cases atRight : right value <;>
        simp [eventMass, union, inter, atLeft, atRight, Nat.add_assoc] at inductionHypothesis ⊢ <;>
        omega

/-- Two observed subevents expose target mass, with their actual overlap
counted only once.  No conditioning or positive-overlap premise is used. -/
theorem eventMass_exposure (atoms : List (Ω × Nat)) (left right target : Event Ω)
    (leftImplies : forall value, left value = true → target value = true)
    (rightImplies : forall value, right value = true → target value = true) :
    eventMass atoms left + eventMass atoms right ≤
      eventMass atoms target + eventMass atoms (inter left right) := by
  have included := eventMass_mono atoms (union left right) target (fun value selected => by
    rcases Bool.or_eq_true_iff.mp selected with atLeft | atRight
    · exact leftImplies value atLeft
    · exact rightImplies value atRight)
  calc
    _ = eventMass atoms (union left right) + eventMass atoms (inter left right) :=
      (eventMass_union_add_inter atoms left right).symm
    _ ≤ _ := Nat.add_le_add_right included _

end FiniteProbRecord
end Probability
end Thesis
