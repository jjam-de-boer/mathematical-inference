import Thesis.Probability.RationalNorm

namespace Thesis.Probability.QProb

/-- A small positive natural bound computed by division, without reducing or
choosing a normalized rational representative. -/
def naturalUpper (value : QProb) : Nat := value.num / value.den + 1

theorem naturalUpper_pos (value : QProb) : 0 < value.naturalUpper := Nat.zero_lt_succ _

theorem le_naturalUpper (value : QProb) : LE value (ofNat value.naturalUpper) := by
  have division := Nat.div_add_mod value.num value.den
  have remainder := Nat.mod_lt value.num value.den_pos
  have expanded : (value.num / value.den + 1) * value.den = value.den * (value.num / value.den) + value.den := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (value.num / value.den)]
  change value.num * 1 ≤ (value.num / value.den + 1) * value.den
  rw [Nat.mul_one, expanded]
  omega

end Thesis.Probability.QProb
