import Thesis.Probability.ConstructiveRealEqualityConstraints
import Thesis.Probability.ConstructiveRealIntegralPairing

namespace Thesis.Probability.Distros.RationalLinear
open ConstructiveReal

/-- Include the rational bound in denominator clearing. Both the resulting
response coefficients and bound are integral, and the common scale is
explicit and positive. No least denominator or reduced representation is
required. -/
def RationalConstraint.fullData (row : RationalConstraint variables) : Fin (variables + 1) → SignedRatio :=
  fun i => if before : i.val < variables then row.coefficients ⟨i.val, before⟩ else row.bound

def RationalConstraint.fullClear (row : RationalConstraint variables) : FiniteDenominatorClearing.Cleared row.fullData :=
  FiniteDenominatorClearing.clear row.fullData

def RationalConstraint.fullScale (row : RationalConstraint variables) : ConstructiveReal :=
  realInteger (row.fullClear.denominator : Int)

def RationalConstraint.fullCoefficient (row : RationalConstraint variables) (i : Fin variables) : Int := row.fullClear.numerator i.castSucc

def RationalConstraint.fullBound (row : RationalConstraint variables) : Int := row.fullClear.numerator (Fin.last variables)

def RationalConstraint.fullLower (row : RationalConstraint variables) : PositiveRatio :=
  .ofNat row.fullClear.denominator row.fullClear.positive

theorem RationalConstraint.fullScale_lower (row : RationalConstraint variables) :
    LE (ofSignedRatio row.fullLower.toSignedRatio) row.fullScale := le_refl _

theorem RationalConstraint.fullScale_nonnegative (row : RationalConstraint variables) : LE zero row.fullScale :=
  (ofSignedRatio_le_iff _ _).mpr ((SignedRatio.zero_le_iff_nonnegative _).mpr (Int.natCast_nonneg _))

private theorem fullData_castSucc (row : RationalConstraint variables) (i : Fin variables) : row.fullData i.castSucc = row.coefficients i := by
  simp only [RationalConstraint.fullData, Fin.val_castSucc, dif_pos i.isLt]

private theorem fullData_last (row : RationalConstraint variables) : row.fullData (Fin.last variables) = row.bound := by
  simp only [RationalConstraint.fullData, Fin.val_last, dif_neg (Nat.lt_irrefl variables)]

private theorem scale_represents (numerator : Int) (denominator : Nat) (positive : 0 < denominator) (value : SignedRatio)
    (represents : SignedRatio.Equiv ⟨numerator, denominator, positive⟩ value) :
    Equiv (mul (realInteger (denominator : Int)) (ofSignedRatio value)) (realInteger numerator) :=
  equiv_trans (ofSignedRatio_mul _ _) ((ofSignedRatio_equiv_iff _ _).mpr (by
    simp only [SignedRatio.Equiv, SignedRatio.mul, Nat.one_mul, Int.natCast_one, Int.mul_one]
    change (denominator : Int) * value.num = numerator * (value.den : Int)
    exact (Int.mul_comm _ _).trans represents.symm))

theorem RationalConstraint.fullCoefficient_scaled (row : RationalConstraint variables) (i : Fin variables) :
    Equiv (mul row.fullScale (ofSignedRatio (row.coefficients i))) (realInteger (row.fullCoefficient i)) :=
  scale_represents _ _ row.fullClear.positive _ (by simpa only [fullData_castSucc] using row.fullClear.represents i.castSucc)

theorem RationalConstraint.fullBound_scaled (row : RationalConstraint variables) :
    Equiv (mul row.fullScale (ofSignedRatio row.bound)) (realInteger row.fullBound) :=
  scale_represents _ _ row.fullClear.positive _ (by simpa only [fullData_last] using row.fullClear.represents (Fin.last variables))

/-- Original rational response evaluation is multiplied by the same positive
scale as its bound, with exact analytic equivalence. -/
theorem RationalConstraint.fullDot_scaled (row : RationalConstraint variables) (values : Fin variables → ConstructiveReal) :
    Equiv (realDot variables row.fullCoefficient values) (mul row.fullScale (realRationalDot variables row.coefficients values)) :=
  equiv_trans (FiniteLinear.realDot_pair variables row.fullCoefficient values)
    (equiv_trans (FiniteLinear.pair_congr variables _ _ values values
      (fun i => equiv_symm (row.fullCoefficient_scaled i)) (fun _ => equiv_refl _))
      (equiv_trans (FiniteLinear.pair_scale_first variables row.fullScale _ values)
        (mul_congr (equiv_refl _) (equiv_symm (realRationalDot_pair variables row.coefficients values)))))

theorem RationalConstraint.fullHolds_iff (row : RationalConstraint variables) (values : Fin variables → ConstructiveReal) :
    LE (realDot variables row.fullCoefficient values) (realInteger row.fullBound) ↔ row.RealHolds values :=
  (le_congr (row.fullDot_scaled values) (equiv_symm row.fullBound_scaled)).trans
    (mul_le_mul_positive_iff row.fullScale row.fullLower row.fullScale_lower _ _)

/-- Weighted slack is invariant under this exact positive row scaling. -/
theorem RationalConstraint.fullSlack_scaled (row : RationalConstraint variables) (values : Fin variables → ConstructiveReal) :
    Equiv (sub (realInteger row.fullBound) (realDot variables row.fullCoefficient values))
      (mul row.fullScale (sub (ofSignedRatio row.bound) (realRationalDot variables row.coefficients values))) :=
  equiv_trans (add_congr (equiv_symm row.fullBound_scaled) (neg_congr (row.fullDot_scaled values)))
    (equiv_symm (mul_sub _ _ _))

end Thesis.Probability.Distros.RationalLinear
