import Thesis.Probability.ConstructiveRealExpAddition
import Thesis.Probability.ConstructiveRealOrderedRing
import Thesis.Probability.ConstructiveRealBounds
import Thesis.Probability.ConstructiveRealReciprocal

namespace Thesis.Probability.ConstructiveReal

/-- Exponentials are nonnegative because every exponential is the square
of the exponential at half its argument. No real sign comparison is used. -/
theorem exp_nonnegative (x : ConstructiveReal) : LE zero x.exp := by
  let half := mul (ofSignedRatio ⟨1, 2, by decide⟩) x
  have coefficient : Equiv (add (ofSignedRatio ⟨1, 2, by decide⟩) (ofSignedRatio ⟨1, 2, by decide⟩)) one :=
    equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel))
  have doubled : Equiv (add half half) x :=
    equiv_trans (equiv_symm (add_mul _ _ x)) (equiv_trans (mul_congr coefficient (equiv_refl x)) (one_mul x))
  have square : Equiv (mul half.exp half.exp) x.exp :=
    equiv_trans (equiv_symm (exp_add half half)) (exp_congr doubled)
  exact (le_congr (equiv_refl zero) square).mp (square_nonnegative half.exp)

/-- A computed positive rational lower bound for exp(x), obtained from a
finite enclosure of exp(-x). This supplies domain data, not a sign decision. -/
def expLower (x : ConstructiveReal) : PositiveRatio :=
  (PositiveRatio.ofNat (neg x).exp.naturalUpper (neg x).exp.naturalUpper_pos).inv

theorem exp_lower (x : ConstructiveReal) : LE (ofSignedRatio x.expLower.toSignedRatio) x.exp := by
  let size := PositiveRatio.ofNat (neg x).exp.naturalUpper (neg x).exp.naturalUpper_pos
  let factor := ofSignedRatio size.toSignedRatio
  have compared := mul_le_mul_nonnegative (exp_nonnegative x) (neg x).exp.le_naturalUpper
  have oneBound : LE one (mul x.exp factor) :=
    (le_congr (exp_mul_exp_neg x) (equiv_refl _)).mp compared
  have canceled : Equiv (mul factor (ofSignedRatio size.inv.toSignedRatio)) one :=
    equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (PositiveRatio.signed_mul_inv size))
  have multiplied : LE (mul factor (ofSignedRatio size.inv.toSignedRatio)) (mul factor x.exp) :=
    (le_congr canceled (mul_comm factor x.exp)).mpr oneBound
  exact (mul_le_mul_positive_iff factor size (le_refl factor) _ _).mp multiplied

/-- The negative exponential equals the constructed positive reciprocal,
with its positive lower-bound witness supplied by the preceding theorem. -/
theorem exp_positiveInverse (x : ConstructiveReal) :
    Equiv (x.exp.positiveInverse x.expLower x.exp_lower) (neg x).exp :=
  inverse_unique _ _ _ (x.exp.mul_positiveInverse x.expLower x.exp_lower) (exp_mul_exp_neg x)


/-- Subtracting arguments divides their exponentials, using the actually
constructed positive inverse and its computed domain certificate. -/
theorem exp_sub (x y : ConstructiveReal) :
    Equiv (exp (sub x y)) (mul x.exp (y.exp.positiveInverse y.expLower y.exp_lower)) :=
  equiv_trans (exp_add x (neg y)) (mul_congr (equiv_refl x.exp) (equiv_symm (exp_positiveInverse y)))

end Thesis.Probability.ConstructiveReal
