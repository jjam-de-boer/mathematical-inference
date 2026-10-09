import Thesis.Probability.Core

namespace Thesis
namespace Probability
namespace FiniteRatioPerturbation

/-!
# Exact changes of finite normalized ratios

A positive change in a joint mass need not change a conditional ratio: the
conditioning mass may change in the same proportion.  The relevant quantity
is the cross-product of the joint change with the old conditioning mass,
minus the old joint mass times the conditioning change.

The masses remain natural numbers.  Their changes are integers only to
retain both signs without truncated natural subtraction; no signed measure
or negative probability is introduced.  The two displayed change identities
refer to the same old and new masses, not independently supplied numerator
and denominator models.  The algebra below neither assumes equal evidence
masses nor infers a separating ratio from joint separation alone.
-/

/-- Exact criterion for cancellation of a joint-mass change after
conditioning.  No positivity is needed for this cross-product identity;
support must be checked separately before interpreting either ratio. -/
theorem cross_eq_iff_balanced (leftJoint leftCondition rightJoint rightCondition : Nat)
    (jointChange conditionChange : Int)
    (joint : (rightJoint : Int) = (leftJoint : Int) + jointChange)
    (condition : (rightCondition : Int) = (leftCondition : Int) + conditionChange) :
    leftJoint * rightCondition = rightJoint * leftCondition ↔
      jointChange * (leftCondition : Int) = (leftJoint : Int) * conditionChange := by
  constructor
  · intro equal
    have cast := congrArg (fun value : Nat => (value : Int)) equal
    simp only [Int.natCast_mul] at cast
    rw [joint, condition, Int.mul_add, Int.add_mul] at cast
    omega
  · intro balanced
    apply Int.ofNat_inj.mp
    simp only [Int.natCast_mul]
    rw [joint, condition, Int.mul_add, Int.add_mul]
    omega

/-- A nonzero normalized change certifies genuinely different ratios.
The premise concerns both actual changes, so it also applies when neither
the joint mass nor the conditioning mass is unchanged. -/
theorem cross_ne_of_normalizedChange_ne_zero
    (leftJoint leftCondition rightJoint rightCondition : Nat)
    (jointChange conditionChange : Int)
    (joint : (rightJoint : Int) = (leftJoint : Int) + jointChange)
    (condition : (rightCondition : Int) = (leftCondition : Int) + conditionChange)
    (nonzero : jointChange * (leftCondition : Int) - (leftJoint : Int) * conditionChange ≠ 0) :
    leftJoint * rightCondition ≠ rightJoint * leftCondition := by
  intro equal
  have balanced := (cross_eq_iff_balanced leftJoint leftCondition rightJoint rightCondition
    jointChange conditionChange joint condition).mp equal
  apply nonzero
  omega

end FiniteRatioPerturbation
end Probability
end Thesis
