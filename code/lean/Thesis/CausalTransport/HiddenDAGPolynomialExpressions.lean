import Thesis.CausalTransport.HiddenDAGPolynomial

namespace Thesis
namespace Causality

open Probability

/-!
# Signed polynomial expressions in native causal probabilities

An event probability is only one useful target. Differences such as an
average treatment effect require signed arithmetic, and products can occur
when a supported conditional bound is cross-multiplied. The expression type
below keeps those operations separate from probability records: a negative
effect is never interpreted as a negative atom weight.

All primitive queries share the same source-cell encoding. Compilation uses
their actual native intervention readouts, and the semantic theorem is proved
by induction through every expression constructor. Constants, sums, negatives
and products are permitted; division is deliberately absent. A conditional
target still needs a separate positive-denominator argument.

The polynomial is independent of the source weights, but not of the finite
source presentation or structural equations. Source-law invariance therefore
supports fixed-template bounds, not a claim about every mechanism on a graph.
-/

inductive NativePolynomialExpression (S : ObservedSignature) where
  | constant : SignedRatio → NativePolynomialExpression S
  | probability : NativeProbabilityQuery S → NativePolynomialExpression S
  | add : NativePolynomialExpression S → NativePolynomialExpression S → NativePolynomialExpression S
  | neg : NativePolynomialExpression S → NativePolynomialExpression S
  | mul : NativePolynomialExpression S → NativePolynomialExpression S → NativePolynomialExpression S

def NativePolynomialExpression.sub (left right : NativePolynomialExpression S) : NativePolynomialExpression S :=
  .add left (.neg right)

namespace FiniteHiddenDAGSCM

/-- The shared source-cell encoding depends on finite noise types and their
enumerations, not on either the query or the source probability weights. -/
def polynomialEncoding (model : FiniteHiddenDAGSCM S projection) :=
  FiniteProbabilityPolynomial.encoding model.noiseEnumeration model.noise_complete model.noiseDecidableEq

def polynomialParameters (model : FiniteHiddenDAGSCM S projection) : Fin model.polynomialEncoding.card → SignedRatio :=
  FiniteProbabilityPolynomial.sourceParameters model.sourceLaw model.noiseDecidableEq model.polynomialEncoding

def polynomialSourceEquations (model : FiniteHiddenDAGSCM S projection) :
    Fin projection.hiddenDAG.count → RationalPolynomial.Polynomial model.polynomialEncoding.card :=
  FiniteProbabilityPolynomial.normalization model.noiseEnumeration model.noiseDecidableEq
    (FiniteProbabilityPolynomial.sourceCode model.polynomialEncoding)

def expressionValue (model : FiniteHiddenDAGSCM S projection) : NativePolynomialExpression S → SignedRatio
  | .constant value => value
  | .probability query => (model.interventionalValue query.intervention query.event).toSignedRatio
  | .add left right => SignedRatio.add (model.expressionValue left) (model.expressionValue right)
  | .neg expression => SignedRatio.neg (model.expressionValue expression)
  | .mul left right => SignedRatio.mul (model.expressionValue left) (model.expressionValue right)

def expressionPolynomial (model : FiniteHiddenDAGSCM S projection) :
    NativePolynomialExpression S → RationalPolynomial.Polynomial model.polynomialEncoding.card
  | .constant value => RationalPolynomial.constant value
  | .probability query => (model.probabilityProgram query).polynomial
  | .add left right => RationalPolynomial.add (model.expressionPolynomial left) (model.expressionPolynomial right)
  | .neg expression => RationalPolynomial.neg (model.expressionPolynomial expression)
  | .mul left right => RationalPolynomial.mul (model.expressionPolynomial left) (model.expressionPolynomial right)

/-- Compilation preserves the actual signed causal expression, not merely
the numeric value at a collection of test assignments. Each probability leaf
uses the native causal compiler's proved semantic correspondence. -/
theorem expressionPolynomial_sound (model : FiniteHiddenDAGSCM S projection) (expression : NativePolynomialExpression S) :
    SignedRatio.Equiv (RationalPolynomial.evaluate (model.expressionPolynomial expression) model.polynomialParameters)
      (model.expressionValue expression) := by
  induction expression with
  | constant value => exact RationalPolynomial.evaluate_constant value model.polynomialParameters
  | probability query => exact model.probabilityProgram_sound query
  | add left right leftSound rightSound =>
      exact SignedRatio.equiv_trans (RationalPolynomial.evaluate_add _ _ model.polynomialParameters)
        (SignedRatio.add_congr leftSound rightSound)
  | neg expression expressionSound =>
      exact SignedRatio.equiv_trans (RationalPolynomial.evaluate_neg _ model.polynomialParameters)
        (SignedRatio.neg_congr expressionSound)
  | mul left right leftSound rightSound =>
      exact SignedRatio.equiv_trans (RationalPolynomial.evaluate_mul _ _ model.polynomialParameters)
        (SignedRatio.mul_congr leftSound rightSound)

theorem polynomialParameters_nonnegative (model : FiniteHiddenDAGSCM S projection) (index : Fin model.polynomialEncoding.card) :
    SignedRatio.Nonnegative (model.polynomialParameters index) :=
  FiniteProbabilityPolynomial.sourceParameters_nonnegative model.sourceLaw model.noiseDecidableEq model.polynomialEncoding index

theorem polynomialSourceEquations_vanish (model : FiniteHiddenDAGSCM S projection) (index : Fin projection.hiddenDAG.count) :
    SignedRatio.Equiv (RationalPolynomial.evaluate (model.polynomialSourceEquations index) model.polynomialParameters) SignedRatio.zero :=
  FiniteProbabilityPolynomial.normalization_sound model.sourceLaw model.noiseEnumeration model.noise_complete model.noiseDecidableEq
    (FiniteProbabilityPolynomial.sourceCode model.polynomialEncoding) model.polynomialParameters
    (FiniteProbabilityPolynomial.sourceParameters_binding model.sourceLaw model.noiseDecidableEq model.polynomialEncoding) index

theorem expressionPolynomial_withSourceLaw (model : FiniteHiddenDAGSCM S projection)
    (law : FiniteProduct.IndependentLaw model.Noise) (expression : NativePolynomialExpression S) :
    (model.withSourceLaw law).expressionPolynomial expression = model.expressionPolynomial expression := by
  induction expression with
  | constant => rfl
  | probability query => exact model.probabilityProgram_polynomial_withSourceLaw law query
  | add left right leftSame rightSame =>
      simp only [expressionPolynomial, leftSame, rightSame]
      rfl
  | neg expression expressionSame => exact congrArg RationalPolynomial.neg expressionSame
  | mul left right leftSame rightSame =>
      simp only [expressionPolynomial, leftSame, rightSame]
      rfl

end FiniteHiddenDAGSCM
end Causality
end Thesis
