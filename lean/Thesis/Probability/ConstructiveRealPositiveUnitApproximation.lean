import Thesis.Probability.ConstructiveRealUnitApproximation
import Thesis.Probability.ConstructiveRealIntervalPartition
import Thesis.Probability.ConstructiveRealPolynomialExpression

namespace Thesis.Probability.ConstructiveReal

private def smoothingLeft (n : Nat) : QProb := ⟨n + 1, n + 2, by omega⟩
private def smoothingRight (n : Nat) : QProb := ⟨1, n + 2, by omega⟩

/-- Mix a rational unit mass with one by a strictly positive rational amount.
This preserves the upper bound one and removes zero scalar inputs. -/
def smoothUnitMass (mass : QProb) (n : Nat) : QProb := QProb.add (QProb.mul (smoothingLeft n) mass) (smoothingRight n)

private theorem smoothing_normalized (n : Nat) : QProb.Equiv (QProb.add (smoothingLeft n) (smoothingRight n)) QProb.one :=
  QProb.equiv_trans (QProb.add_mk_same_den (n + 2) (by omega) (n + 1) 1) (by
    change (n + 1 + 1) * 1 = 1 * (n + 2)
    omega)

theorem smoothUnitMass_positive (mass : QProb) (n : Nat) : 0 < (smoothUnitMass mass n).num := by
  change 0 < ((n + 1) * mass.num) * (n + 2) + 1 * ((n + 2) * mass.den)
  have positive := Nat.mul_pos (show 0 < n + 2 by omega) mass.den_pos
  omega

theorem smoothUnitMass_bounded (mass : QProb) (bounded : mass.num ≤ mass.den) (n : Nat) :
    (smoothUnitMass mass n).num ≤ (smoothUnitMass mass n).den := by
  have massBound : QProb.LE mass QProb.one := by
    simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using bounded
  have first := QProb.le_congr (QProb.equiv_refl _) (QProb.mul_one (smoothingLeft n))
    (QProb.mul_le_mul (QProb.le_refl (smoothingLeft n)) massBound)
  have all := QProb.le_congr (QProb.equiv_refl _) (smoothing_normalized n) (QProb.add_le_add first (QProb.le_refl (smoothingRight n)))
  simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using all

private abbrev Expr := RationalPolynomial.Expression 3
private def pVar : Expr := .coordinate 0
private def tVar : Expr := .coordinate 1
private def uVar : Expr := .coordinate 2
private def smoothingExpr : Expr := .add (.mul tVar pVar) uVar
private def intervalExpr : Expr := .add (.mul pVar (.add tVar uVar)) (.mul uVar (.sub (.constant SignedRatio.one) pVar))

private theorem smoothing_identity (p t u : ConstructiveReal) :
    Equiv (add (mul t p) u) (add (mul p (add t u)) (mul u (sub one p))) :=
  RationalPolynomial.Expression.equalityCheck_sound_real smoothingExpr intervalExpr (by decide +kernel)
    (fun index => match index.val with | 0 => p | 1 => t | _ => u)

private theorem smoothUnitMass_value (mass : QProb) (n : Nat) :
    Equiv (ofSignedRatio (smoothUnitMass mass n).toSignedRatio)
      (intervalPoint (ofSignedRatio mass.toSignedRatio) one (n + 2) (by omega) 1) := by
  let p := ofSignedRatio mass.toSignedRatio
  let t := ofSignedRatio (smoothingLeft n).toSignedRatio
  let u := ofSignedRatio (smoothingRight n).toSignedRatio
  have represented : Equiv (ofSignedRatio (smoothUnitMass mass n).toSignedRatio) (add (mul t p) u) := by
    unfold smoothUnitMass
    rw [QProb.toSignedRatio_add, QProb.toSignedRatio_mul]
    exact equiv_symm (equiv_trans (add_congr (ofSignedRatio_mul _ _) (equiv_refl _)) (ofSignedRatio_add _ _))
  have rational := QProb.toSignedRatio_congr (smoothing_normalized n)
  rw [QProb.toSignedRatio_add, QProb.toSignedRatio_one] at rational
  have normalized : Equiv (add t u) one :=
    equiv_trans (ofSignedRatio_add _ _) ((ofSignedRatio_equiv_iff _ _).mpr rational)
  exact equiv_trans represented (equiv_trans (smoothing_identity p t u)
    (add_congr (equiv_trans (mul_congr (equiv_refl p) normalized) (mul_one p)) (equiv_refl _)))

theorem smoothUnitMass_within (mass : QProb) (bounded : mass.num ≤ mass.den) (n : Nat) :
    Within (PositiveRatio.unitPrecision (n + 1)).toQProb (ofSignedRatio mass.toSignedRatio) (ofSignedRatio (smoothUnitMass mass n).toSignedRatio) := by
  let p := ofSignedRatio mass.toSignedRatio
  have positive : LE zero p := (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff _ _).mpr (QProb.zero_le mass))
  have unit : LE p one := (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.toSignedRatio_le_iff mass QProb.one).mpr
    (by simpa only [QProb.LE, QProb.one, Nat.mul_one, Nat.one_mul] using bounded))
  have close := intervalPoint_within p one unit (interval_width_le_one p one positive (le_refl one)) (n + 2) (by omega) 0
  exact (within_congr (intervalPoint_zero p one (n + 2) (by omega)) (equiv_symm (smoothUnitMass_value mass n))).mp close

/-- A strictly positive rational approximation of any scalar unit-interval
real at a requested precision. The positive lower bound may tend to zero;
no positivity or zero test is requested of the original real. -/
def positiveUnitCenter (x : ConstructiveReal) (precision : PositiveRatio) : QProb :=
  smoothUnitMass (x.unitCenter precision.half) precision.half.den

theorem positiveUnitCenter_positive (x : ConstructiveReal) (precision : PositiveRatio) : 0 < (x.positiveUnitCenter precision).num :=
  smoothUnitMass_positive _ _

theorem positiveUnitCenter_bounded (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one) (precision : PositiveRatio) :
    (x.positiveUnitCenter precision).num ≤ (x.positiveUnitCenter precision).den :=
  smoothUnitMass_bounded _ (x.unitCenter_bounded nonnegative bounded precision.half) _

theorem positiveUnitCenter_within (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one) (precision : PositiveRatio) :
    Within precision.toQProb x (ofSignedRatio (x.positiveUnitCenter precision).toSignedRatio) := by
  have smoothed := smoothUnitMass_within (x.unitCenter precision.half) (x.unitCenter_bounded nonnegative bounded precision.half) precision.half.den
  have smaller := PositiveRatio.unitPrecision_le precision.half (precision.half.den + 1) (Nat.le_succ _)
  exact within_triangle_halves precision (x.unitCenter_within nonnegative precision.half) (within_mono smoothed smaller)

def positiveUnitSequence (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one) : RealCauchySequence where
  value n := ofSignedRatio (x.positiveUnitCenter (PositiveRatio.unitPrecision n)).toSignedRatio
  modulus precision := precision.half.den
  cauchy precision n m left right := by
    have compared := within_triangle (within_symm (x.positiveUnitCenter_within nonnegative bounded (PositiveRatio.unitPrecision n)))
      (x.positiveUnitCenter_within nonnegative bounded (PositiveRatio.unitPrecision m))
    have smaller := QProb.add_le_add (PositiveRatio.unitPrecision_le precision.half n left) (PositiveRatio.unitPrecision_le precision.half m right)
    exact within_mono compared (QProb.le_congr (QProb.equiv_refl _) precision.half_sum smaller)

theorem positiveUnitSequence_limit (x : ConstructiveReal) (nonnegative : LE zero x) (bounded : LE x one) : Equiv (x.positiveUnitSequence nonnegative bounded).limit x := by
  apply RealCauchySequence.limit_unique _ _ (fun precision => precision.den)
  intro precision n later
  exact within_mono (within_symm (x.positiveUnitCenter_within nonnegative bounded (PositiveRatio.unitPrecision n)))
    (PositiveRatio.unitPrecision_le precision n later)

end Thesis.Probability.ConstructiveReal
