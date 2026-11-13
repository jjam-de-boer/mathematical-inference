import Thesis.Probability.ExactLogRational

namespace Thesis.Probability.ExactLog

/-- A dyadic number of bits, with its positive denominator retained explicitly. -/
def dyadic (numerator : Int) (steps : Nat) : SignedRatio :=
  ⟨numerator, 2 ^ steps, Nat.pow_pos (by decide)⟩

theorem dyadic_double (numerator : Int) (steps : Nat) :
    SignedRatio.Equiv (dyadic (2 * numerator) (steps + 1)) (dyadic numerator steps) := by
  change (2 * numerator) * ((2 ^ steps : Nat) : Int) = numerator * ((2 ^ (steps + 1) : Nat) : Int)
  rw [Nat.pow_succ, Int.natCast_mul]
  change (2 * numerator) * ((2 ^ steps : Nat) : Int) = numerator * (((2 ^ steps : Nat) : Int) * 2)
  ac_rfl

/-- Width of the inexpensive initial bracket in bits. -/
def initialWidth (x : ExactLog) : Nat := (x.argument.num.log2 + 1) + (x.argument.den.log2 + 1)

/-- Bounds at a prescribed finite bisection depth. The width is exactly
`initialWidth x / 2^steps`, so the certificate also covers values near zero. -/
structure DyadicBracket (x : ExactLog) (steps : Nat) where
  lower : Int
  lower_bound : LE (ofSignedRatio (dyadic lower steps)) x
  upper_bound : LE x (ofSignedRatio (dyadic (lower + (initialWidth x : Int)) steps))

/-- Certified bisection. Each step uses an exact rational-power comparison. -/
def bisect (x : ExactLog) : (steps : Nat) → DyadicBracket x steps
  | 0 => {
      lower := -((x.argument.den.log2 + 1 : Nat) : Int)
      lower_bound := natural_lower x
      upper_bound := by
        have endpoint : -((x.argument.den.log2 + 1 : Nat) : Int) + (initialWidth x : Int) = ((x.argument.num.log2 + 1 : Nat) : Int) := by
          change -((x.argument.den.log2 + 1 : Nat) : Int) +
            (((x.argument.num.log2 + 1 : Nat) : Int) + ((x.argument.den.log2 + 1 : Nat) : Int)) =
            ((x.argument.num.log2 + 1 : Nat) : Int)
          rw [Int.add_comm ((x.argument.num.log2 + 1 : Nat) : Int) ((x.argument.den.log2 + 1 : Nat) : Int),
            Int.neg_add_cancel_left]
        rw [endpoint]
        exact natural_upper x }
  | steps + 1 =>
      let previous := bisect x steps
      let midpoint := 2 * previous.lower + (initialWidth x : Int)
      if left : LE x (ofSignedRatio (dyadic midpoint (steps + 1))) then {
        lower := 2 * previous.lower
        lower_bound := (le_congr (ofSignedRatio_congr (dyadic_double previous.lower steps)) (equiv_refl x)).mpr previous.lower_bound
        upper_bound := left }
      else {
        lower := midpoint
        lower_bound := by
          rcases le_total x (ofSignedRatio (dyadic midpoint (steps + 1))) with forward | backward
          · exact False.elim (left forward)
          · exact backward
        upper_bound := by
          have endpoint : midpoint + (initialWidth x : Int) = 2 * (previous.lower + (initialWidth x : Int)) := by
            dsimp [midpoint]
            rw [Int.mul_add, Int.two_mul (initialWidth x : Int)]
            exact Int.add_assoc _ _ _
          rw [endpoint]
          exact (le_congr (equiv_refl x)
            (ofSignedRatio_congr (dyadic_double (previous.lower + (initialWidth x : Int)) steps))).mpr previous.upper_bound }

/-- An executable rational interval, strictly narrower than the requested
positive rational tolerance. Both endpoints share the explicit denominator. -/
structure Enclosure (x : ExactLog) (tolerance : QProb) where
  lower : Int
  width : Nat
  den : Nat
  den_pos : 0 < den
  lower_bound : LE (ofSignedRatio ⟨lower, den, den_pos⟩) x
  upper_bound : LE x (ofSignedRatio ⟨lower + (width : Int), den, den_pos⟩)
  width_lt : width * tolerance.den < tolerance.num * den

/-- Total approximation at every positive rational tolerance. A binary-length
bound selects a sufficient finite depth before any rational-power bisection. -/
def enclose (x : ExactLog) (tolerance : QProb) (positive : 0 < tolerance.num) : Enclosure x tolerance := by
  let target := initialWidth x * tolerance.den
  let steps := target.log2 + 1
  let bracket := bisect x steps
  refine ⟨bracket.lower, initialWidth x, 2 ^ steps, Nat.pow_pos (by decide),
    bracket.lower_bound, bracket.upper_bound, ?_⟩
  have base : target < 2 ^ steps := Nat.lt_log2_self
  have raised : 2 ^ steps ≤ tolerance.num * 2 ^ steps := Nat.le_mul_of_pos_left _ positive
  exact Nat.lt_of_lt_of_le base raised

end Thesis.Probability.ExactLog
