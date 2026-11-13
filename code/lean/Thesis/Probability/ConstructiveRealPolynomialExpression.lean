import Thesis.Probability.RationalPolynomialExpression
import Thesis.Probability.RationalApproximationSequence
import Thesis.Probability.ConstructiveRealDifferenceLimits
import Thesis.Probability.ConstructiveRealProductLimits

namespace Thesis.Probability.RationalPolynomial.Expression
open ConstructiveReal
variable {variables : Nat}

/-- Interpret the same finite rational-coefficient expression in constructed
real arithmetic. This does not change rational probability weights. -/
def evaluateReal (values : Fin variables → ConstructiveReal) : Expression variables → ConstructiveReal
  | .constant value => ofSignedRatio value
  | .coordinate index => values index
  | .add left right => ConstructiveReal.add (evaluateReal values left) (evaluateReal values right)
  | .sub left right => ConstructiveReal.sub (evaluateReal values left) (evaluateReal values right)
  | .mul left right => ConstructiveReal.mul (evaluateReal values left) (evaluateReal values right)

theorem evaluateReal_congr (expression : Expression variables) (first second : Fin variables → ConstructiveReal)
    (same : ∀ index, Equiv (first index) (second index)) : Equiv (expression.evaluateReal first) (expression.evaluateReal second) := by
  induction expression with
  | constant value => exact equiv_refl _
  | coordinate index => exact same index
  | add left right ihLeft ihRight => exact add_congr ihLeft ihRight
  | sub left right ihLeft ihRight => exact add_congr ihLeft (neg_congr ihRight)
  | mul left right ihLeft ihRight => exact mul_congr ihLeft ihRight

theorem evaluateReal_ofSignedRatio (expression : Expression variables) (values : Fin variables → SignedRatio) :
    Equiv (expression.evaluateReal (fun index => ofSignedRatio (values index))) (ofSignedRatio (expression.evaluate values)) := by
  induction expression with
  | constant value => exact equiv_refl _
  | coordinate index => exact equiv_refl _
  | add left right ihLeft ihRight => exact equiv_trans (add_congr ihLeft ihRight) (ofSignedRatio_add _ _)
  | sub left right ihLeft ihRight => exact equiv_trans (add_congr ihLeft (neg_congr ihRight)) (ofSignedRatio_sub _ _)
  | mul left right ihLeft ihRight => exact equiv_trans (mul_congr ihLeft ihRight) (ofSignedRatio_mul _ _)

/-- Evaluate an expression along effective input sequences. Every product
modulus and its required tail bound is supplied by the existing limit rules. -/
def evaluationSequence (values : Fin variables → RealCauchySequence) : Expression variables → RealCauchySequence
  | .constant value => RealCauchySequence.constant (ofSignedRatio value)
  | .coordinate index => values index
  | .add left right => (evaluationSequence values left).add (evaluationSequence values right)
  | .sub left right => (evaluationSequence values left).sub (evaluationSequence values right)
  | .mul left right => (evaluationSequence values left).mul (evaluationSequence values right)

theorem evaluationSequence_value (expression : Expression variables) (values : Fin variables → RealCauchySequence) (n : Nat) :
    (expression.evaluationSequence values).value n = expression.evaluateReal (fun index => (values index).value n) := by
  induction expression with
  | constant value => rfl
  | coordinate index => rfl
  | add left right ihLeft ihRight =>
      change ConstructiveReal.add _ _ = ConstructiveReal.add _ _
      rw [ihLeft, ihRight]
  | sub left right ihLeft ihRight =>
      change ConstructiveReal.sub _ _ = ConstructiveReal.sub _ _
      rw [ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      change ConstructiveReal.mul _ _ = ConstructiveReal.mul _ _
      rw [ihLeft, ihRight]

theorem evaluationSequence_limit (expression : Expression variables) (values : Fin variables → RealCauchySequence) :
    Equiv (expression.evaluationSequence values).limit (expression.evaluateReal (fun index => (values index).limit)) := by
  induction expression with
  | constant value => exact RealCauchySequence.constant_limit _
  | coordinate index => exact equiv_refl _
  | add left right ihLeft ihRight => exact equiv_trans (RealCauchySequence.add_limit _ _) (add_congr ihLeft ihRight)
  | sub left right ihLeft ihRight => exact equiv_trans (RealCauchySequence.sub_limit _ _) (add_congr ihLeft (neg_congr ihRight))
  | mul left right ihLeft ihRight => exact equiv_trans (RealCauchySequence.mul_limit _ _) (mul_congr ihLeft ihRight)

/-- An accepted finite rational polynomial identity holds at every real
assignment. The proof transfers the universal rational identity through
explicitly convergent rational approximations and polynomial limit rules;
it performs no equality or sign test on real inputs. -/
theorem equalityCheck_sound_real (left right : Expression variables) (checked : equalityCheck left right = true)
    (values : Fin variables → ConstructiveReal) : Equiv (left.evaluateReal values) (right.evaluateReal values) := by
  let sequences : Fin variables → RealCauchySequence := fun index => (values index).rationalSequence
  have same (n : Nat) : Equiv ((left.evaluationSequence sequences).value n) ((right.evaluationSequence sequences).value n) := by
    rw [evaluationSequence_value, evaluationSequence_value]
    let rationals : Fin variables → SignedRatio := fun index => (values index).rationalApproximation.sequence.value n
    exact equiv_trans (evaluateReal_ofSignedRatio left rationals)
      (equiv_trans ((ofSignedRatio_equiv_iff _ _).mpr (equalityCheck_sound left right checked rationals))
        (equiv_symm (evaluateReal_ofSignedRatio right rationals)))
  have limitLeft : Equiv (left.evaluationSequence sequences).limit (left.evaluateReal values) :=
    equiv_trans (evaluationSequence_limit left sequences) (evaluateReal_congr left _ _ (fun index => (values index).rationalSequence_limit))
  have limitRight : Equiv (right.evaluationSequence sequences).limit (right.evaluateReal values) :=
    equiv_trans (evaluationSequence_limit right sequences) (evaluateReal_congr right _ _ (fun index => (values index).rationalSequence_limit))
  exact equiv_trans (equiv_symm limitLeft)
    (equiv_trans (RealCauchySequence.limit_congr _ _ same) limitRight)

end Thesis.Probability.RationalPolynomial.Expression
