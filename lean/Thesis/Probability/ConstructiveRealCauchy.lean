import Thesis.Probability.ConstructiveRealAdditionLimits

namespace Thesis.Probability.PositiveRatio

theorem half_sum (precision : PositiveRatio) :
    QProb.Equiv (QProb.add precision.half.toQProb precision.half.toQProb) precision.toQProb := by
  apply (QProb.toSignedRatio_equiv_iff _ _).mp
  rw [QProb.toSignedRatio_add]
  exact precision.half_add_half

end Thesis.Probability.PositiveRatio

namespace Thesis.Probability.ConstructiveReal

theorem within_refl (error : QProb) (x : ConstructiveReal) : Within error x x := by
  have nonnegative : LE zero (ofSignedRatio error.toSignedRatio) :=
    (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le error))
  have increased : LE x (add x (ofSignedRatio error.toSignedRatio)) :=
    (le_congr (add_zero x) (equiv_refl _)).mp (add_le_add (le_refl x) nonnegative)
  exact ⟨increased, increased⟩

/-- The lower endpoint is a certified rational approximation of the real. -/
theorem lower_within (x : ConstructiveReal) (precision : PositiveRatio) :
    Within precision.toQProb x (ofSignedRatio (x.enclose precision).lower) :=
  (within_congr x.rationalApproximation_limit (equiv_refl _)).mp
    (x.rationalApproximation.limit_within precision)

theorem within_triangle_halves (precision : PositiveRatio) {x y z : ConstructiveReal}
    (first : Within precision.half.toQProb x y) (second : Within precision.half.toQProb y z) :
    Within precision.toQProb x z :=
  within_mono (within_triangle first second)
    (QProb.le_congr (QProb.equiv_refl _) precision.half_sum (QProb.le_refl _))

end Thesis.Probability.ConstructiveReal

namespace Thesis.Probability

/-- A real-valued Cauchy sequence includes its executable modulus and a
proved two-sided tail estimate. No real comparison or countable choice is used. -/
structure RealCauchySequence where
  value : Nat → ConstructiveReal
  modulus : PositiveRatio → Nat
  cauchy : ∀ precision n m, modulus precision ≤ n → modulus precision ≤ m →
    ConstructiveReal.Within precision.toQProb (value n) (value m)

namespace RealCauchySequence
open ConstructiveReal

/-- Select a sufficiently late real value, then compute a rational endpoint.
A common later index compares different requested precisions; the supplied
modulus need not be monotone. -/
def regular (sequence : RealCauchySequence) : RegularRationalApproximation where
  value precision := (sequence.value (sequence.modulus precision.half)).enclose precision.half |>.lower
  regular first second := by
    let later := max (sequence.modulus first.half) (sequence.modulus second.half)
    have left := within_triangle_halves first
      (within_symm ((sequence.value (sequence.modulus first.half)).lower_within first.half))
      (sequence.cauchy first.half (sequence.modulus first.half) later (Nat.le_refl _) (Nat.le_max_left _ _))
    have right := within_triangle_halves second
      (sequence.cauchy second.half later (sequence.modulus second.half) (Nat.le_max_right _ _) (Nat.le_refl _))
      ((sequence.value (sequence.modulus second.half)).lower_within second.half)
    exact ((SignedRatio.magnitude_sub_le_iff _ _ _).mp
      ((within_ofSignedRatio_iff _ _ _).mp (within_triangle left right))).1

def limit (sequence : RealCauchySequence) : ConstructiveReal := sequence.regular.limit

/-- An explicit tail bound for the constructed real limit. -/
theorem tail_within (sequence : RealCauchySequence) (precision : PositiveRatio) (n : Nat)
    (later : sequence.modulus precision.half.half ≤ n) :
    Within precision.toQProb (sequence.value n) sequence.limit := by
  have toCenter := within_triangle_halves precision.half
    (sequence.cauchy precision.half.half n (sequence.modulus precision.half.half) later (Nat.le_refl _))
    ((sequence.value (sequence.modulus precision.half.half)).lower_within precision.half.half)
  exact within_triangle_halves precision toCenter
    (within_symm (sequence.regular.limit_within precision.half))

/-- Uniqueness consumes an explicit convergence modulus for the competing
limit, rather than selecting indices from propositional existence. -/
theorem limit_unique (sequence : RealCauchySequence) (x : ConstructiveReal)
    (modulus : PositiveRatio → Nat)
    (converges : ∀ precision n, modulus precision ≤ n → Within precision.toQProb (sequence.value n) x) :
    Equiv sequence.limit x := by
  apply equiv_of_within_all
  intro precision
  let n := max (sequence.modulus precision.half.half.half) (modulus precision.half)
  exact within_triangle_halves precision
    (within_symm (sequence.tail_within precision.half n (Nat.le_max_left _ _)))
    (converges precision.half n (Nat.le_max_right _ _))

/-- Equivalent terms give equivalent limits even if their moduli differ. -/
theorem limit_congr (first second : RealCauchySequence)
    (same : ∀ n, Equiv (first.value n) (second.value n)) : Equiv first.limit second.limit := by
  apply first.limit_unique second.limit (fun precision => second.modulus precision.half.half)
  intro precision n later
  exact (within_congr (equiv_symm (same n)) (equiv_refl _)).mp (second.tail_within precision n later)

/-- Constant real sequences have a computable zero modulus. -/
def constant (x : ConstructiveReal) : RealCauchySequence where
  value _ := x
  modulus _ := 0
  cauchy precision _ _ _ _ := within_refl precision.toQProb x

theorem constant_limit (x : ConstructiveReal) : Equiv (constant x).limit x :=
  (constant x).limit_unique x (fun _ => 0) (fun precision _ _ => within_refl precision.toQProb x)

/-- Pointwise addition preserves effective Cauchy convergence. -/
def add (first second : RealCauchySequence) : RealCauchySequence where
  value n := ConstructiveReal.add (first.value n) (second.value n)
  modulus precision := max (first.modulus precision.half) (second.modulus precision.half)
  cauchy precision n m left right := by
    have compared := within_add
      (first.cauchy precision.half n m (Nat.le_trans (Nat.le_max_left _ _) left) (Nat.le_trans (Nat.le_max_left _ _) right))
      (second.cauchy precision.half n m (Nat.le_trans (Nat.le_max_right _ _) left) (Nat.le_trans (Nat.le_max_right _ _) right))
    exact within_mono compared (QProb.le_congr (QProb.equiv_refl _) precision.half_sum (QProb.le_refl _))

/-- The constructed limit of a sum is the sum of its independently
constructed limits. -/
theorem add_limit (first second : RealCauchySequence) :
    Equiv (first.add second).limit (ConstructiveReal.add first.limit second.limit) := by
  apply limit_unique _ _ (fun precision => max (first.modulus precision.half.half.half) (second.modulus precision.half.half.half))
  intro precision n later
  have compared := within_add
    (first.tail_within precision.half n (Nat.le_trans (Nat.le_max_left _ _) later))
    (second.tail_within precision.half n (Nat.le_trans (Nat.le_max_right _ _) later))
  exact within_mono compared (QProb.le_congr (QProb.equiv_refl _) precision.half_sum (QProb.le_refl _))

/-- A finite family of effective sequences has an effective sum sequence. -/
def listSum : List RealCauchySequence → RealCauchySequence
  | [] => constant ConstructiveReal.zero
  | first :: rest => first.add (listSum rest)

theorem listSum_value (sequences : List RealCauchySequence) (n : Nat) :
    (listSum sequences).value n = ConstructiveReal.listSum (sequences.map (fun sequence => sequence.value n)) := by
  induction sequences with
  | nil => rfl
  | cons first rest ih => exact congrArg (ConstructiveReal.add (first.value n)) ih

/-- Effective limits commute with every finite sum. -/
theorem listSum_limit (sequences : List RealCauchySequence) :
    Equiv (listSum sequences).limit (ConstructiveReal.listSum (sequences.map (fun sequence => sequence.limit))) := by
  induction sequences with
  | nil => exact constant_limit ConstructiveReal.zero
  | cons first rest ih => exact equiv_trans (add_limit first (listSum rest)) (add_congr (equiv_refl _) ih)

end RealCauchySequence

namespace RationalCauchySequence

/-- Embed an effective rational sequence without altering its modulus. -/
def toReal (sequence : RationalCauchySequence) : RealCauchySequence where
  value n := ConstructiveReal.ofSignedRatio (sequence.value n)
  modulus := sequence.modulus
  cauchy precision n m left right :=
    (ConstructiveReal.within_ofSignedRatio_iff _ _ _).mpr
      ((SignedRatio.magnitude_sub_le_iff _ _ _).mpr
        ⟨sequence.cauchy precision n m left right, sequence.cauchy precision m n right left⟩)

/-- Completing before or after the real embedding gives the same value. -/
theorem toReal_limit (sequence : RationalCauchySequence) :
    ConstructiveReal.Equiv sequence.toReal.limit sequence.limit := by
  apply sequence.toReal.limit_unique sequence.limit (fun precision => sequence.modulus precision.half)
  intro precision n later
  have bounds := sequence.tail_bounds precision n later
  constructor
  · have shifted := ConstructiveReal.add_le_add bounds.1
      (ConstructiveReal.le_refl (ConstructiveReal.ofSignedRatio precision.toSignedRatio))
    have reduced : ConstructiveReal.Equiv
        (ConstructiveReal.add (ConstructiveReal.ofSignedRatio (SignedRatio.sub (sequence.value n) precision.toSignedRatio))
          (ConstructiveReal.ofSignedRatio precision.toSignedRatio))
        (ConstructiveReal.ofSignedRatio (sequence.value n)) :=
      ConstructiveReal.equiv_trans (ConstructiveReal.ofSignedRatio_add _ _)
      ((ConstructiveReal.ofSignedRatio_equiv_iff _ _).mpr (SignedRatio.sub_add_cancel _ _))
    exact (ConstructiveReal.le_congr reduced (ConstructiveReal.equiv_refl _)).mp shifted
  · exact (ConstructiveReal.le_congr (ConstructiveReal.equiv_refl _) (ConstructiveReal.ofSignedRatio_add _ _)).mpr bounds.2

end RationalCauchySequence
end Thesis.Probability
