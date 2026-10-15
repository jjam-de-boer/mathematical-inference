import Thesis.Probability.RationalMonomial

namespace Thesis
namespace Probability
namespace RationalPolynomial

variable {variables : Nat}

/-!
# Sparse rational polynomials with proved exact evaluation

A polynomial is an explicit finite list of rational-coefficient monomials.
Repeated monomials and zero coefficients are permitted; operations do not
assume that a caller has supplied a normalized list.  Natural exponent vectors
already account for commuting variables, and signed rational coefficients
retain their own positive denominators.

The evaluation theorems connect the actual list constructors to finite signed
rational algebra.  A later checker may collect equal monomials and test their
coefficients, but its semantic soundness must use these proved operations;
syntactic resemblance to a probability formula is not a semantic premise.
-/

structure Term (variables : Nat) where
  coefficient : SignedRatio
  powers : RationalMonomial.Powers variables

abbrev Polynomial (variables : Nat) := List (Term variables)

def Term.evaluate (term : Term variables) (values : Fin variables → SignedRatio) : SignedRatio :=
  SignedRatio.mul term.coefficient (RationalMonomial.evaluate term.powers values)

def Term.multiply (left right : Term variables) : Term variables :=
  ⟨SignedRatio.mul left.coefficient right.coefficient, RationalMonomial.combine left.powers right.powers⟩

def evaluate (polynomial : Polynomial variables) (values : Fin variables → SignedRatio) : SignedRatio :=
  SignedRatio.listSum (polynomial.map fun term => term.evaluate values)

def zero (variables : Nat) : Polynomial variables := []
def constant (value : SignedRatio) : Polynomial variables := [⟨value, RationalMonomial.unit variables⟩]
def coordinate (chosen : Fin variables) : Polynomial variables := [⟨SignedRatio.one, RationalMonomial.coordinate chosen⟩]
def add (left right : Polynomial variables) : Polynomial variables := left ++ right
def neg (polynomial : Polynomial variables) : Polynomial variables :=
  polynomial.map (fun term => ⟨SignedRatio.neg term.coefficient, term.powers⟩)
def sub (left right : Polynomial variables) : Polynomial variables := add left (neg right)
def mul (left right : Polynomial variables) : Polynomial variables :=
  left.flatMap (fun first => right.map (fun second => first.multiply second))

theorem evaluate_singleton (term : Term variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate [term] values) (term.evaluate values) := SignedRatio.add_zero _

theorem evaluate_constant (value : SignedRatio) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate (constant value) values) value :=
  SignedRatio.equiv_trans (evaluate_singleton _ values)
    (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl value) (RationalMonomial.evaluate_unit variables values))
      (SignedRatio.mul_one value))

theorem evaluate_coordinate (chosen : Fin variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate (coordinate chosen) values) (values chosen) :=
  SignedRatio.equiv_trans (evaluate_singleton _ values)
    (SignedRatio.equiv_trans (SignedRatio.mul_congr (SignedRatio.equiv_refl SignedRatio.one) (RationalMonomial.evaluate_coordinate chosen values))
      (SignedRatio.one_mul _))

theorem evaluate_add (left right : Polynomial variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate (add left right) values) (SignedRatio.add (evaluate left values) (evaluate right values)) := by
  simp only [evaluate, add, List.map_append]
  exact SignedRatio.listSum_append _ _

theorem evaluate_neg (polynomial : Polynomial variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate (neg polynomial) values) (SignedRatio.neg (evaluate polynomial values)) := by
  have congruent := SignedRatio.listSum_map_congr polynomial
    (fun term => (⟨SignedRatio.neg term.coefficient, term.powers⟩ : Term variables).evaluate values)
    (fun term => SignedRatio.neg (term.evaluate values))
    (fun term => SignedRatio.neg_mul term.coefficient (RationalMonomial.evaluate term.powers values))
  exact SignedRatio.equiv_trans (by
    simpa only [evaluate, neg, List.map_map, Function.comp_def] using congruent)
    (by simpa only [List.map_map, Function.comp_def, evaluate] using
      SignedRatio.listSum_map_neg (polynomial.map fun term => term.evaluate values))

theorem evaluate_sub (left right : Polynomial variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate (sub left right) values) (SignedRatio.sub (evaluate left values) (evaluate right values)) :=
  SignedRatio.equiv_trans (evaluate_add left (neg right) values)
    (SignedRatio.add_congr (SignedRatio.equiv_refl _) (evaluate_neg right values))

theorem Term.evaluate_multiply (left right : Term variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv ((left.multiply right).evaluate values) (SignedRatio.mul (left.evaluate values) (right.evaluate values)) :=
  SignedRatio.equiv_trans
    (SignedRatio.mul_congr (SignedRatio.equiv_refl _) (RationalMonomial.evaluate_combine left.powers right.powers values))
    (SignedRatio.mul_interchange left.coefficient right.coefficient _ _)

theorem evaluate_mul_row (first : Term variables) (right : Polynomial variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate (right.map first.multiply) values) (SignedRatio.mul (first.evaluate values) (evaluate right values)) := by
  have congruent := SignedRatio.listSum_map_congr right
    (fun second => (first.multiply second).evaluate values)
    (fun second => SignedRatio.mul (first.evaluate values) (second.evaluate values))
    (fun second => first.evaluate_multiply second values)
  exact SignedRatio.equiv_trans (by simpa only [evaluate, List.map_map, Function.comp_def] using congruent)
    (by simpa only [evaluate, List.map_map, Function.comp_def] using
      SignedRatio.equiv_symm (SignedRatio.mul_listSum (first.evaluate values) (right.map fun term => term.evaluate values)))

theorem evaluate_mul (left right : Polynomial variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (evaluate (mul left right) values) (SignedRatio.mul (evaluate left values) (evaluate right values)) := by
  have flattened := SignedRatio.listSum_flatMap left
    (fun first => (right.map first.multiply).map fun term => term.evaluate values)
  have rows := SignedRatio.listSum_map_congr left
    (fun first => evaluate (right.map first.multiply) values)
    (fun first => SignedRatio.mul (first.evaluate values) (evaluate right values))
    (fun first => evaluate_mul_row first right values)
  refine SignedRatio.equiv_trans (by
    simpa only [evaluate, mul, List.map_flatMap] using flattened) (SignedRatio.equiv_trans rows ?_)
  simpa only [evaluate, List.map_map, Function.comp_def] using
    SignedRatio.equiv_symm (SignedRatio.listSum_mul (left.map fun term => term.evaluate values) (evaluate right values))

end RationalPolynomial
end Probability
end Thesis
