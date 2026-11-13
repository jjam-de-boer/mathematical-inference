import Thesis.Probability.ConstructiveRealEntropyDerivative
import Thesis.Probability.ConstructiveRealEntropySum
import Thesis.Probability.ConstructiveDerivativeWithinChain
import Thesis.Probability.ConstructiveDerivativeScaling

namespace Thesis.Probability.ConstructiveReal

/-- An affine coordinate path. These are auxiliary analytic coordinates;
this construction does not change the rational probability weight type. -/
def affineCoordinate (mass direction parameter : ConstructiveReal) : ConstructiveReal :=
  add (mul parameter direction) mass

theorem affineCoordinate_zero (mass direction : ConstructiveReal) :
    Equiv (affineCoordinate mass direction zero) mass :=
  equiv_trans (add_congr (zero_mul direction) (equiv_refl _)) (zero_add mass)

/-- The formula is valid on the supplied positive part of the finite cube.
Normalization and linear expectations can further restrict this domain. -/
def entropyLineDomain (masses directions : Fin variables → ConstructiveReal) (lower : Fin variables → PositiveRatio)
    (parameter : ConstructiveReal) : Prop :=
  ∀ i, entropyPositiveDomain (lower i) (affineCoordinate (masses i) (directions i) parameter)

theorem entropyLineDomain_zero (masses directions : Fin variables → ConstructiveReal) (lower : Fin variables → PositiveRatio)
    (inside : ∀ i, entropyPositiveDomain (lower i) (masses i)) : entropyLineDomain masses directions lower zero := by
  intro i
  exact ⟨(le_congr (equiv_refl _) (affineCoordinate_zero _ _)).mpr (inside i).1,
    (le_congr (affineCoordinate_zero _ _) (equiv_refl _)).mpr (inside i).2⟩

def entropyLine (masses directions : Fin variables → ConstructiveReal) (lower : Fin variables → PositiveRatio)
    (parameter : ConstructiveReal) (inside : entropyLineDomain masses directions lower parameter) : ConstructiveReal :=
  realEntropySum ((List.finRange variables).map (fun i =>
    ⟨affineCoordinate (masses i) (directions i) parameter,
      entropyPositiveNonnegative (lower i) _ (inside i), (inside i).2⟩))

/-- The bit-unit entropy gradient on a certified positive coordinate. -/
def entropyBitGradient (mass : ConstructiveReal) (lower : PositiveRatio)
    (positive : LE (ofSignedRatio lower.toSignedRatio) mass) : ConstructiveReal :=
  neg (add (mass.positiveLog2 lower positive) RationalLogSecant.limit)

def entropyNaturalGradient (mass : ConstructiveReal) (lower : PositiveRatio)
    (positive : LE (ofSignedRatio lower.toSignedRatio) mass) : ConstructiveReal :=
  neg (add (mass.positiveLn lower positive) one)

theorem entropyGradient_units (mass : ConstructiveReal) (lower : PositiveRatio)
    (positive : LE (ofSignedRatio lower.toSignedRatio) mass) :
    Equiv (mul (entropyBitGradient mass lower positive) lnTwo) (entropyNaturalGradient mass lower positive) :=
  equiv_trans (neg_mul _ lnTwo) (neg_congr (equiv_trans (add_mul _ _ lnTwo)
    (add_congr (equiv_refl _) coefficient_mul_lnTwo)))

/-- Full finite first variation in bits. Its slope is the sum of the
coordinate directions times `-log₂(pᵢ)-1/ln(2)`. All error moduli come from
the proved affine, scalar-entropy, chain and finite-sum rules. This alone
asserts neither that the path is feasible nor that its slope is zero. -/
def entropyLine_hasDerivativeWithinAt (masses directions : Fin variables → ConstructiveReal)
    (lower : Fin variables → PositiveRatio) (inside : ∀ i, entropyPositiveDomain (lower i) (masses i)) :
    HasDerivativeWithinAt (entropyLineDomain masses directions lower) (entropyLine masses directions lower)
      zero (entropyLineDomain_zero masses directions lower inside)
      (listSum ((List.finRange variables).map (fun i => mul (directions i) (entropyBitGradient (masses i) (lower i) (inside i).1)))) := by
  let domain := entropyLineDomain masses directions lower
  let atZero := entropyLineDomain_zero masses directions lower inside
  have coordinate (i : Fin variables) :
      HasDerivativeWithinAt domain
        (fun t admitted => (affineCoordinate (masses i) (directions i) t).realEntropyTerm
          (entropyPositiveNonnegative (lower i) _ (admitted i)) (admitted i).2)
        zero atZero (mul (directions i) (entropyBitGradient (masses i) (lower i) (inside i).1)) := by
    let affine := (HasDerivativeAt.affine zero (directions i) (masses i)).restrict domain atZero
    let scalar := realEntropyTerm_hasDerivativeWithinAt _ (lower i) (atZero i)
    let composed := affine.chainWithin scalar (fun t admitted => admitted i)
    have logarithm := positiveLog2_congr (affineCoordinate_zero (masses i) (directions i)) (lower i) (lower i)
      (atZero i).1 (inside i).1
    exact composed.slope_congr (mul_congr (equiv_refl _) (neg_congr (add_congr logarithm (equiv_refl _))))
  have total := HasDerivativeWithinAt.listSum (List.finRange variables) _ _ zero atZero coordinate
  exact total.function_congr (fun _ _ => by
    simp only [entropyLine, realEntropySum, List.map_map, UnitIntervalValue.entropy]
    exact equiv_refl _)

/-- Conversion of the entire first variation to natural entropy units,
including the additive normalization term in each coordinate gradient. -/
theorem entropyFirstVariation_units (indices : List ι) (masses directions : ι → ConstructiveReal)
    (lower : ι → PositiveRatio) (positive : ∀ i, LE (ofSignedRatio (lower i).toSignedRatio) (masses i)) :
    Equiv (mul (listSum (indices.map (fun i => mul (directions i) (entropyBitGradient (masses i) (lower i) (positive i))))) lnTwo)
      (listSum (indices.map (fun i => mul (directions i) (entropyNaturalGradient (masses i) (lower i) (positive i))))) :=
  equiv_trans (listSum_mul _ lnTwo)
    (by
      simp only [List.map_map]
      exact listSum_map_congr indices _ _ (fun i _ =>
        equiv_trans (mul_assoc _ _ _) (mul_congr (equiv_refl _) (entropyGradient_units _ _ _))))

/-- Actual finite natural-entropy differentiation has the converted
slope, with an effective remainder certificate rather than only a formal
change of gradient notation. -/
def naturalEntropyLine_hasDerivativeWithinAt (masses directions : Fin variables → ConstructiveReal)
    (lower : Fin variables → PositiveRatio) (inside : ∀ i, entropyPositiveDomain (lower i) (masses i)) :
    HasDerivativeWithinAt (entropyLineDomain masses directions lower)
      (fun parameter supplied => mul (entropyLine masses directions lower parameter supplied) lnTwo)
      zero (entropyLineDomain_zero masses directions lower inside)
      (listSum ((List.finRange variables).map (fun i => mul (directions i) (entropyNaturalGradient (masses i) (lower i) (inside i).1)))) :=
  ((entropyLine_hasDerivativeWithinAt masses directions lower inside).mul_constant lnTwo).slope_congr
    (entropyFirstVariation_units _ masses directions lower (fun i => (inside i).1))

end Thesis.Probability.ConstructiveReal
