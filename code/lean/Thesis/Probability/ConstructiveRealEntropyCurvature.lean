import Thesis.Probability.ConstructiveRealEntropyUniformDerivative

namespace Thesis.Probability.ConstructiveReal

private def halfRatio : SignedRatio := ⟨1, 2, by decide⟩
private def halfValue : ConstructiveReal := ofSignedRatio halfRatio
private abbrev Expr1 := RationalPolynomial.Expression 1
private def doubleHalf : Expr1 := .mul (.add (.coordinate 0) (.coordinate 0)) (.constant halfRatio)
private theorem double_half (x : ConstructiveReal) : Equiv (mul (add x x) halfValue) x :=
  RationalPolynomial.Expression.equalityCheck_sound_real doubleHalf (.coordinate 0) (by decide +kernel) (fun _ => x)

/-- The quadratic correction is an analytic proof device: entropy plus
p²/2 will have decreasing slope on each positive part of [0,1]. -/
def adjustedEntropy (lower : PositiveRatio) (x : ConstructiveReal) (inside : entropyPositiveDomain lower x) : ConstructiveReal :=
  add (x.realEntropyTerm (entropyPositiveNonnegative lower x inside) inside.2) (mul (mul x x) halfValue)

def adjustedEntropySlope (lower : PositiveRatio) (x : ConstructiveReal) (inside : entropyPositiveDomain lower x) : ConstructiveReal :=
  sub x (add (x.positiveLog2 lower inside.1) RationalLogSecant.limit)

def adjustedEntropy_uniformDerivative (lower : PositiveRatio) :
    UniformDerivativeWithin (entropyPositiveDomain lower) (adjustedEntropy lower) (adjustedEntropySlope lower) := by
  let quadratic := (square_uniformDerivative (entropyPositiveDomain lower)).mul_constant halfValue
  let total := (realEntropyTerm_uniformDerivative lower).add quadratic
  exact total.slope_congr (fun x _ => equiv_trans (add_congr (equiv_refl _) (double_half x)) (add_comm _ _))

private abbrev Expr5 := RationalPolynomial.Expression 5
private def xVar : Expr5 := .coordinate 0
private def yVar : Expr5 := .coordinate 1
private def lxVar : Expr5 := .coordinate 2
private def lyVar : Expr5 := .coordinate 3
private def cVar : Expr5 := .coordinate 4
private def slopeGap : Expr5 := .sub (.sub xVar (.add lxVar cVar)) (.sub yVar (.add lyVar cVar))
private def incrementGap : Expr5 := .sub (.sub lyVar lxVar) (.sub yVar xVar)
private theorem slope_gap (x y lx ly c : ConstructiveReal) :
    Equiv (sub (sub x (add lx c)) (sub y (add ly c))) (sub (sub ly lx) (sub y x)) :=
  RationalPolynomial.Expression.equalityCheck_sound_real slopeGap incrementGap (by decide +kernel)
    (fun index => match index.val with | 0 => x | 1 => y | 2 => lx | 3 => ly | _ => c)

/-- The logarithm increment bound gives the required quantitative decrease
of the entropy slope, expressed as ordinary concavity of the corrected function. -/
theorem adjustedEntropy_slope_antitone (x y : ConstructiveReal) (lower : PositiveRatio)
    (insideX : entropyPositiveDomain lower x) (insideY : entropyPositiveDomain lower y) (ordered : LE x y) :
    LE (adjustedEntropySlope lower y insideY) (adjustedEntropySlope lower x insideX) := by
  have increment := positiveLog2_increment_lower x y lower insideX.1 insideY.1 ordered insideY.2
  have positive := (zero_le_sub_iff _ _).mpr increment
  have gap := slope_gap x y (x.positiveLog2 lower insideX.1) (y.positiveLog2 lower insideY.1) RationalLogSecant.limit
  exact (zero_le_sub_iff _ _).mp ((le_congr (equiv_refl zero) gap).mpr positive)

theorem adjustedEntropy_tangent_right (point y : ConstructiveReal) (lower : PositiveRatio)
    (inside : entropyPositiveDomain lower point) (insideY : entropyPositiveDomain lower y) (ordered : LE point y) :
    LE (adjustedEntropy lower y insideY)
      (add (adjustedEntropy lower point inside) (mul (sub y point) (adjustedEntropySlope lower point inside))) :=
  (adjustedEntropy_uniformDerivative lower).upper_bound point y (adjustedEntropySlope lower point inside) ordered
    (interval_width_le_one point y (entropyPositiveNonnegative lower point inside) insideY.2)
    (fun _ above below => ⟨le_trans inside.1 above, le_trans below insideY.2⟩)
    (fun z hz above _ => adjustedEntropy_slope_antitone point z lower inside hz above)

theorem adjustedEntropy_tangent_left (x point : ConstructiveReal) (lower : PositiveRatio)
    (insideX : entropyPositiveDomain lower x) (inside : entropyPositiveDomain lower point) (ordered : LE x point) :
    LE (adjustedEntropy lower x insideX)
      (add (adjustedEntropy lower point inside) (mul (sub x point) (adjustedEntropySlope lower point inside))) := by
  let slope := adjustedEntropySlope lower point inside
  let increment := mul (sub point x) slope
  have estimate := (adjustedEntropy_uniformDerivative lower).lower_bound x point slope ordered
    (interval_width_le_one x point (entropyPositiveNonnegative lower x insideX) inside.2)
    (fun _ above below => ⟨le_trans insideX.1 above, le_trans below inside.2⟩)
    (fun z hz _ below => adjustedEntropy_slope_antitone z point lower hz inside below)
  have reversed : Equiv (neg (sub point x)) (sub x point) :=
    equiv_trans (neg_add _ _) (equiv_trans (add_congr (equiv_refl _) (neg_neg x)) (add_comm _ _))
  have negativeIncrement : Equiv (neg increment) (mul (sub x point) slope) :=
    equiv_trans (equiv_symm (neg_mul _ _)) (mul_congr reversed (equiv_refl slope))
  have cancel : Equiv (add (add (adjustedEntropy lower x insideX) increment) (neg increment)) (adjustedEntropy lower x insideX) :=
    equiv_trans (add_assoc _ _ _) (equiv_trans (add_congr (equiv_refl _) (add_neg increment)) (add_zero _))
  exact (le_congr cancel (add_congr (equiv_refl _) negativeIncrement)).mp
    (add_le_add estimate (le_refl (neg increment)))

/-- The real midpoint uses the same rational half coefficient as actual
finite-law mixtures. It introduces no irrational probability record. -/
def midpoint (x y : ConstructiveReal) : ConstructiveReal := mul (add x y) halfValue

theorem midpoint_self (x : ConstructiveReal) : Equiv (midpoint x x) x := double_half x

theorem midpoint_comm (x y : ConstructiveReal) : Equiv (midpoint x y) (midpoint y x) :=
  mul_congr (add_comm x y) (equiv_refl halfValue)

/-- Unit bounds pass to a midpoint without an endpoint order hypothesis. -/
theorem midpoint_unit (x y : ConstructiveReal) (nonnegativeX : LE zero x) (nonnegativeY : LE zero y)
    (boundedX : LE x one) (boundedY : LE y one) : LE zero (midpoint x y) ∧ LE (midpoint x y) one := by
  have halfNonnegative : LE zero halfValue := (ofSignedRatio_le_iff _ _).mpr (by decide +kernel)
  have sumNonnegative : LE zero (add x y) := (le_congr (zero_add zero) (equiv_refl _)).mp (add_le_add nonnegativeX nonnegativeY)
  exact ⟨mul_nonnegative sumNonnegative halfNonnegative,
    (le_congr (equiv_refl _) (midpoint_self one)).mp (mul_le_mul_nonnegative_right halfNonnegative (add_le_add boundedX boundedY))⟩

private abbrev Expr2 := RationalPolynomial.Expression 2
private def midpointExpr : Expr2 := .mul (.add (.coordinate 0) (.coordinate 1)) (.constant halfRatio)
private def intervalMidpointExpr : Expr2 := .add (.coordinate 0)
  (.mul (.constant halfRatio) (.sub (.coordinate 1) (.coordinate 0)))

theorem midpoint_bounds (x y : ConstructiveReal) (ordered : LE x y) : LE x (midpoint x y) ∧ LE (midpoint x y) y := by
  have partition : Equiv (midpoint x y) (intervalPoint x y 2 (by decide) 1) :=
    RationalPolynomial.Expression.equalityCheck_sound_real midpointExpr intervalMidpointExpr (by decide +kernel)
      (fun index => if index.val = 0 then x else y)
  have bounded := intervalPoint_bounds x y ordered 2 (by decide) 1 (by decide)
  exact ⟨(le_congr (equiv_refl _) partition).mpr bounded.1, (le_congr partition (equiv_refl _)).mpr bounded.2⟩

theorem midpoint_inside (x y : ConstructiveReal) (lower : PositiveRatio)
    (insideX : entropyPositiveDomain lower x) (insideY : entropyPositiveDomain lower y) (ordered : LE x y) :
    entropyPositiveDomain lower (midpoint x y) :=
  ⟨le_trans insideX.1 (midpoint_bounds x y ordered).1, le_trans (midpoint_bounds x y ordered).2 insideY.2⟩

private abbrev Expr4 := RationalPolynomial.Expression 4
private def midpoint4 : Expr4 := .mul (.add (.coordinate 0) (.coordinate 1)) (.constant halfRatio)
private def midpointTangentSum : Expr4 := .add
  (.add (.coordinate 2) (.mul (.sub (.coordinate 0) midpoint4) (.coordinate 3)))
  (.add (.coordinate 2) (.mul (.sub (.coordinate 1) midpoint4) (.coordinate 3)))
private def midpointDouble : Expr4 := .add (.coordinate 2) (.coordinate 2)

/-- Tangents at the midpoint cancel their linear terms. -/
theorem adjustedEntropy_midpoint (x y : ConstructiveReal) (lower : PositiveRatio)
    (insideX : entropyPositiveDomain lower x) (insideY : entropyPositiveDomain lower y) (ordered : LE x y) :
    let m := midpoint x y
    let insideM : entropyPositiveDomain lower m :=
      ⟨le_trans insideX.1 (midpoint_bounds x y ordered).1, le_trans (midpoint_bounds x y ordered).2 insideY.2⟩
    LE (add (adjustedEntropy lower x insideX) (adjustedEntropy lower y insideY))
      (add (adjustedEntropy lower m insideM) (adjustedEntropy lower m insideM)) := by
  intro m insideM
  have bounds := midpoint_bounds x y ordered
  have left := adjustedEntropy_tangent_left x m lower insideX insideM bounds.1
  have right := adjustedEntropy_tangent_right m y lower insideM insideY bounds.2
  have cancellation : Equiv
      (add (add (adjustedEntropy lower m insideM) (mul (sub x m) (adjustedEntropySlope lower m insideM)))
        (add (adjustedEntropy lower m insideM) (mul (sub y m) (adjustedEntropySlope lower m insideM))))
      (add (adjustedEntropy lower m insideM) (adjustedEntropy lower m insideM)) :=
    RationalPolynomial.Expression.equalityCheck_sound_real midpointTangentSum midpointDouble (by decide +kernel)
      (fun index => match index.val with | 0 => x | 1 => y | 2 => adjustedEntropy lower m insideM | _ => adjustedEntropySlope lower m insideM)
  exact (le_congr (equiv_refl _) cancellation).mp (add_le_add left right)

end Thesis.Probability.ConstructiveReal
