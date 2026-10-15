import Thesis.Probability.RationalPolynomial

namespace Thesis
namespace Probability
namespace RationalPolynomial

variable {variables : Nat}

/-!
# Finite polynomial families

These explicit finite folds are shared by probability compilation and bound
certificate decomposition.  Their empty cases are respectively zero and one;
no nonempty-family assumption or selected term is required.
-/

def sum : List (Polynomial variables) → Polynomial variables
  | [] => zero variables
  | polynomial :: rest => add polynomial (sum rest)

def product : List (Polynomial variables) → Polynomial variables
  | [] => constant SignedRatio.one
  | polynomial :: rest => mul polynomial (product rest)

theorem evaluate_sum (polynomials : List (Polynomial variables)) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate (sum polynomials) values) (SignedRatio.listSum (polynomials.map fun polynomial => evaluate polynomial values)) := by
  induction polynomials with
  | nil => exact SignedRatio.equiv_refl SignedRatio.zero
  | cons polynomial rest inductionHypothesis =>
      exact SignedRatio.equiv_trans (evaluate_add polynomial (sum rest) values)
        (SignedRatio.add_congr (SignedRatio.equiv_refl _) inductionHypothesis)

theorem evaluate_product (polynomials : List (Polynomial variables)) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate (product polynomials) values) (SignedRatio.listProduct (polynomials.map fun polynomial => evaluate polynomial values)) := by
  induction polynomials with
  | nil => exact evaluate_constant SignedRatio.one values
  | cons polynomial rest inductionHypothesis =>
      exact SignedRatio.equiv_trans (evaluate_mul polynomial (product rest) values)
        (SignedRatio.mul_congr (SignedRatio.equiv_refl _) inductionHypothesis)

end RationalPolynomial
end Probability
end Thesis
