import Thesis.Probability.RationalPolynomialIdentity

namespace Thesis.Probability.RationalPolynomial

/-- Finite signed rational expressions. Compiling these expressions to the
existing sparse-polynomial checker supplies reusable universal algebra proofs;
checking an identity never substitutes numerical samples for its variables. -/
inductive Expression (variables : Nat) where
  | constant : SignedRatio → Expression variables
  | coordinate : Fin variables → Expression variables
  | add : Expression variables → Expression variables → Expression variables
  | sub : Expression variables → Expression variables → Expression variables
  | mul : Expression variables → Expression variables → Expression variables

namespace Expression

def evaluate (values : Fin variables → SignedRatio) : Expression variables → SignedRatio
  | .constant value => value
  | .coordinate index => values index
  | .add left right => SignedRatio.add (evaluate values left) (evaluate values right)
  | .sub left right => SignedRatio.sub (evaluate values left) (evaluate values right)
  | .mul left right => SignedRatio.mul (evaluate values left) (evaluate values right)

def compile : Expression variables → Polynomial variables
  | .constant value => RationalPolynomial.constant value
  | .coordinate index => RationalPolynomial.coordinate index
  | .add left right => RationalPolynomial.add (compile left) (compile right)
  | .sub left right => RationalPolynomial.sub (compile left) (compile right)
  | .mul left right => RationalPolynomial.mul (compile left) (compile right)

theorem compile_sound (expression : Expression variables) (values : Fin variables → SignedRatio) :
    SignedRatio.Equiv (RationalPolynomial.evaluate expression.compile values) (expression.evaluate values) := by
  induction expression with
  | constant value => exact evaluate_constant value values
  | coordinate index => exact evaluate_coordinate index values
  | add left right ihLeft ihRight => exact SignedRatio.equiv_trans (evaluate_add _ _ values) (SignedRatio.add_congr ihLeft ihRight)
  | sub left right ihLeft ihRight => exact SignedRatio.equiv_trans (evaluate_sub _ _ values) (SignedRatio.add_congr ihLeft (SignedRatio.neg_congr ihRight))
  | mul left right ihLeft ihRight => exact SignedRatio.equiv_trans (evaluate_mul _ _ values) (SignedRatio.mul_congr ihLeft ihRight)

def equalityCheck (left right : Expression variables) : Bool := RationalPolynomial.equalityCheck left.compile right.compile

theorem equalityCheck_sound (left right : Expression variables) (checked : equalityCheck left right = true)
    (values : Fin variables → SignedRatio) : SignedRatio.Equiv (left.evaluate values) (right.evaluate values) :=
  SignedRatio.equiv_trans (SignedRatio.equiv_symm (compile_sound left values))
    (SignedRatio.equiv_trans (RationalPolynomial.equalityCheck_sound _ _ checked values) (compile_sound right values))

end Expression
end Thesis.Probability.RationalPolynomial
