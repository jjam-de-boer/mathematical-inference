import Thesis.Probability.ConstructiveRealDualCombinations
import Thesis.Probability.ConstructiveRealIntegralPairing
import Thesis.Probability.ConstructiveRealAffineSimplex
import Thesis.Probability.ConstructiveRealPolynomialExpression

namespace Thesis.Probability.AnalyticLinear
open ConstructiveReal
open Distros.RationalLinear
open IntegerLinearAlgebra

/-- The primal perturbation associated to a canceled dual combination.
Its normalization is zero and its row changes are controlled by the
nonnegative signature cone, without an analytic active-set decision. -/
def DualSignature.perturbation (signature : DualSignature rows columns)
    (masses : Fin columns → ConstructiveReal) (i : Fin columns) : ConstructiveReal :=
  neg (add (realInteger (signature.direction i)) (mul (realInteger signature.total) (masses i)))

theorem DualSignature.perturbation_normalized (signature : DualSignature rows columns)
    (masses : Fin columns → ConstructiveReal)
    (normalized : Equiv (realDot columns (fun _ => 1) masses) one)
    (canceled : dot signature.direction (fun _ => 1) + signature.total = 0) :
    Equiv (realDot columns (fun _ => 1) (signature.perturbation masses)) zero := by
  have integral := realDot_integers columns (fun _ => 1) signature.direction
  rw [dot_comm (fun _ => 1) signature.direction] at integral
  have scaled := equiv_trans (realDot_scale_left_values columns (fun _ => 1) (realInteger signature.total) masses)
    (equiv_trans (mul_congr (equiv_refl _) normalized) (mul_one _))
  have sum := equiv_trans (realDot_add_values columns (fun _ => 1) _ _) (add_congr integral scaled)
  have zeroSum := equiv_trans sum (realInteger_add _ _)
  rw [canceled] at zeroSum
  exact equiv_trans (realDot_neg_values columns (fun _ => 1) _)
    (equiv_trans (neg_congr zeroSum) (equiv_symm (ofSignedRatio_neg SignedRatio.zero)))

/-- Each actual row derivative is expressed using its original integral
bound, current response, and the nonnegative canceled coefficient. -/
theorem DualSignature.perturbation_row (signature : DualSignature rows columns)
    (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (masses : Fin columns → ConstructiveReal)
    (canceled : ∀ r, dot signature.direction (matrix r) + signature.total * bounds r = (signature.cone r : Int)) (r : Fin rows) :
    Equiv (realDot columns (matrix r) (signature.perturbation masses))
      (neg (add (sub (realInteger (signature.cone r : Int)) (mul (realInteger signature.total) (realInteger (bounds r))))
        (mul (realInteger signature.total) (realDot columns (matrix r) masses)))) := by
  have integral := realDot_integers columns (matrix r) signature.direction
  rw [dot_comm (matrix r) signature.direction] at integral
  have integerSame : dot signature.direction (matrix r) = (signature.cone r : Int) - signature.total * bounds r := by
    have actual := canceled r
    omega
  rw [integerSame] at integral
  have integralSame := equiv_trans integral (equiv_trans (equiv_symm (realInteger_sub _ _))
    (add_congr (equiv_refl _) (neg_congr (equiv_symm (realInteger_mul _ _)))))
  exact equiv_trans (realDot_neg_values columns (matrix r) _)
    (neg_congr (equiv_trans (realDot_add_values columns (matrix r) _ _)
      (add_congr integralSame (realDot_scale_left_values columns (matrix r) (realInteger signature.total) masses))))

/-- Pairing the primal perturbation with the gradient is minus the exact
analytic right-hand side of its canceled dual combination. -/
theorem DualSignature.perturbation_pair (signature : DualSignature rows columns)
    (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (masses gradient : Fin columns → ConstructiveReal) :
    Equiv (FiniteLinear.pair columns (signature.perturbation masses) gradient)
      (neg (signature.row matrix bounds gradient (FiniteLinear.pair columns masses gradient)).bound) :=
  equiv_trans (FiniteLinear.pair_neg_first columns _ gradient)
    (neg_congr (equiv_trans (FiniteLinear.pair_add_first columns _ _ gradient)
      (add_congr (equiv_symm (FiniteLinear.realDot_pair columns signature.direction gradient))
        (FiniteLinear.pair_scale_first columns (realInteger signature.total) masses gradient))))

private abbrev Expression := RationalPolynomial.Expression 5
private def boundExpr : Expression := .coordinate 0
private def priorExpr : Expression := .coordinate 1
private def totalExpr : Expression := .coordinate 2
private def parameterExpr : Expression := .coordinate 3
private def coneExpr : Expression := .coordinate 4
private def slopeExpr : Expression := .sub (.constant SignedRatio.zero)
  (.add (.sub coneExpr (.mul totalExpr boundExpr)) (.mul totalExpr priorExpr))
private def slackExpr : Expression := .sub boundExpr (.add (.mul slopeExpr parameterExpr) priorExpr)
private def positiveSlackExpr : Expression := .add
  (.mul (.sub (.constant SignedRatio.one) (.mul parameterExpr totalExpr)) (.sub boundExpr priorExpr))
  (.mul parameterExpr coneExpr)

/-- Exact slack identity behind the constructive duality argument. It is
an algebraic identity, independently checked in the rational polynomial
checker and transferred to analytic values. -/
theorem dual_slack_identity (bound prior total parameter cone : ConstructiveReal) :
    Equiv (sub bound (add (mul (neg (add (sub cone (mul total bound)) (mul total prior))) parameter) prior))
      (add (mul (sub one (mul parameter total)) (sub bound prior)) (mul parameter cone)) := by
  have checked := RationalPolynomial.Expression.equalityCheck_sound_real slackExpr positiveSlackExpr (by decide +kernel)
    (fun i => if i = 0 then bound else if i = 1 then prior else if i = 2 then total else if i = 3 then parameter else cone)
  exact equiv_trans (add_congr (equiv_refl _) (neg_congr (add_congr
    (mul_congr (equiv_symm (zero_add _)) (equiv_refl _)) (equiv_refl _)))) checked

/-- The slack after an affine perturbation is a sum of two nonnegative
terms when `1 - t * total ≥ 0`. This holds for every original row at once,
even when some current slacks vanish and others cannot be classified. -/
theorem DualSignature.perturbation_slack (signature : DualSignature rows columns)
    (matrix : Matrix rows columns) (bounds : Fin rows → Int)
    (masses : Fin columns → ConstructiveReal) (parameter : ConstructiveReal)
    (canceled : ∀ r, dot signature.direction (matrix r) + signature.total * bounds r = (signature.cone r : Int)) (r : Fin rows) :
    Equiv (sub (realInteger (bounds r)) (realDot columns (matrix r)
      (fun i => affineCoordinate (masses i) (signature.perturbation masses i) parameter)))
      (add (mul (sub one (mul parameter (realInteger signature.total)))
        (sub (realInteger (bounds r)) (realDot columns (matrix r) masses)))
        (mul parameter (realInteger (signature.cone r : Int)))) :=
  equiv_trans (add_congr (equiv_refl _) (neg_congr
    (equiv_trans (realDot_affineCoordinate columns (matrix r) masses (signature.perturbation masses) parameter)
      (add_congr (mul_congr (signature.perturbation_row matrix bounds masses canceled r) (equiv_refl _)) (equiv_refl _)))))
    (dual_slack_identity _ _ _ _ _)

end Thesis.Probability.AnalyticLinear
