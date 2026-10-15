import Thesis.Probability.RationalPolynomialIdentity

namespace Thesis
namespace Probability
namespace Examples
namespace RationalPolynomialIdentity

open RationalPolynomial

/-!
# Checked identities are universal, not numerical spot checks

The difference-of-squares identity expands into duplicated mixed monomials
that must cancel, despite their different multiplication order.  A separate
commutativity check tests exponent-vector grouping directly.  Rational constant
cancellation exercises unreduced coefficients and the zero-variable boundary.

The invalid sum-of-squares replacement is explicitly rejected.  All Boolean
decisions below are reduced by the kernel.  Universal identities then follow
from `equalityCheck_sound` for every signed rational parameter assignment,
including negative values and zero denominators nowhere being permitted.
-/

def x : Polynomial 2 := variable 0
def y : Polynomial 2 := variable 1
def differenceProduct := mul (add x y) (sub x y)
def differenceSquares := sub (mul x x) (mul y y)

theorem difference_of_squares_checked : equalityCheck differenceProduct differenceSquares = true := by decide +kernel
theorem difference_of_squares (values : Fin 2 → SignedRatio) :
    SignedRatio.Equiv (evaluate differenceProduct values) (evaluate differenceSquares values) :=
  equalityCheck_sound _ _ difference_of_squares_checked values
theorem commuting_variables_checked : equalityCheck (mul x y) (mul y x) = true := by decide +kernel
theorem incorrect_identity_rejected : equalityCheck differenceProduct (add (mul x x) (mul y y)) = false := by decide +kernel

def fractionalSum : Polynomial 0 := add (constant ⟨1, 2, by decide⟩) (constant ⟨1, 3, by decide⟩)
theorem fractional_coefficients_checked : equalityCheck fractionalSum (constant ⟨5, 6, by decide⟩) = true := by decide +kernel
def unreducedCancellation : Polynomial 0 := add (constant ⟨1, 2, by decide⟩) (constant ⟨-2, 4, by decide⟩)
theorem unreduced_zero_checked : zeroCheck unreducedCancellation = true := by decide +kernel
theorem empty_polynomial_checked : zeroCheck (zero 0) = true := rfl

def signedValues : Fin 2 → SignedRatio := fun index =>
  if index.val = 0 then ⟨-1, 2, by decide⟩ else ⟨2, 3, by decide⟩
theorem signed_value : SignedRatio.Equiv (evaluate differenceProduct signedValues) ⟨-7, 36, by decide⟩ := by decide +kernel

end RationalPolynomialIdentity
end Examples
end Probability
end Thesis
