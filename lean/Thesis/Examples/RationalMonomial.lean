import Thesis.Probability.RationalMonomial

namespace Thesis
namespace Probability
namespace Examples
namespace RationalMonomial

open Probability.RationalMonomial SignedRatio

/-!
# Exact signed monomial and finite-sum regressions

The variables one half and minus two thirds give `x^2 y = -1/6`.
Combining the exponent vector with itself gives its square, one thirty-sixth.
These computations test signed intermediate values and positive denominators
without normalized `Rat`, native Boolean proof reduction or floating point.

Universal product/congruence statements are used separately from the closed
kernel computations, so the fixture does not replace the symbolic algebra
needed to validate a supplied polynomial certificate.
-/

def values : Fin 2 → SignedRatio := fun index =>
  if index.val = 0 then ⟨1, 2, by decide⟩ else ⟨-2, 3, by decide⟩
def powers : Powers 2 := fun index => if index.val = 0 then 2 else 1

theorem signed_value : Equiv (evaluate powers values) ⟨-1, 6, by decide⟩ := by decide +kernel
theorem combined_value : Equiv (evaluate (combine powers powers) values) ⟨1, 36, by decide⟩ := by decide +kernel
theorem product_identity : Equiv (evaluate (combine powers powers) values) (mul (evaluate powers values) (evaluate powers values)) :=
  evaluate_combine powers powers values
theorem empty_product : Equiv (evaluate (unit 0) (fun index => Fin.elim0 index)) one := evaluate_unit 0 _
theorem finite_signed_sum : Equiv (listSum [values 0, values 1]) ⟨-1, 6, by decide⟩ := by decide +kernel
theorem cancelled_difference : Equiv (sub (values 0) ⟨2, 4, by decide⟩) zero :=
  (sub_equiv_zero_iff _ _).mpr (by decide +kernel)

end RationalMonomial
end Examples
end Probability
end Thesis
