import Thesis.Probability.ConstructiveRealPolynomialExpression

namespace Thesis.Probability.ConstructiveReal

def derivativeProductQuarter : SignedRatio := ⟨1, 4, by decide⟩
private abbrev Expr2 := RationalPolynomial.Expression 2
private def xVar : Expr2 := .coordinate 0
private def yVar : Expr2 := .coordinate 1
private def sumVar : Expr2 := .add xVar yVar
private def diffVar : Expr2 := .sub xVar yVar
private def productLeft : Expr2 := .mul (.sub (.mul sumVar sumVar) (.mul diffVar diffVar)) (.constant derivativeProductQuarter)
private def productRight : Expr2 := .mul xVar yVar

theorem derivative_product_value_identity (x y : ConstructiveReal) :
    Equiv (mul (sub (mul (add x y) (add x y)) (mul (sub x y) (sub x y))) (ofSignedRatio derivativeProductQuarter)) (mul x y) :=
  RationalPolynomial.Expression.equalityCheck_sound_real productLeft productRight (by decide +kernel)
    (fun index => if index.val = 0 then x else y)

private abbrev Expr4 := RationalPolynomial.Expression 4
private def fVar : Expr4 := .coordinate 0
private def gVar : Expr4 := .coordinate 1
private def sfVar : Expr4 := .coordinate 2
private def sgVar : Expr4 := .coordinate 3
private def sumValue : Expr4 := .add fVar gVar
private def diffValue : Expr4 := .sub fVar gVar
private def sumSlope : Expr4 := .add sfVar sgVar
private def diffSlope : Expr4 := .sub sfVar sgVar
private def slopeLeft : Expr4 :=
  .mul (.sub (.mul sumSlope (.add sumValue sumValue)) (.mul diffSlope (.add diffValue diffValue))) (.constant derivativeProductQuarter)
private def slopeRight : Expr4 := .add (.mul sfVar gVar) (.mul fVar sgVar)

theorem derivative_product_slope_identity (f g sf sg : ConstructiveReal) :
    Equiv (mul (sub (mul (add sf sg) (add (add f g) (add f g)))
      (mul (sub sf sg) (add (sub f g) (sub f g)))) (ofSignedRatio derivativeProductQuarter))
      (add (mul sf g) (mul f sg)) :=
  RationalPolynomial.Expression.equalityCheck_sound_real slopeLeft slopeRight (by decide +kernel)
    (fun index => match index.val with | 0 => f | 1 => g | 2 => sf | _ => sg)

end Thesis.Probability.ConstructiveReal
