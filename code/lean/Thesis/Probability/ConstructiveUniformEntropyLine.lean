import Thesis.Probability.ConstructiveUniformAffine
import Thesis.Probability.ConstructiveRealEntropyUniformDerivative
import Thesis.Probability.ConstructiveRealEntropyFirstVariation

namespace Thesis.Probability.ConstructiveReal

/-- The actual finite entropy on an affine probability line has a computed
uniform first-variation modulus on its explicit positive cube domain. No
uniformity is inferred from separate pointwise derivatives. -/
def entropyLine_uniformDerivative (masses directions : Fin variables → ConstructiveReal)
    (lower : Fin variables → PositiveRatio) :
    UniformDerivativeWithin (entropyLineDomain masses directions lower) (entropyLine masses directions lower)
      (fun t hx => listSum ((List.finRange variables).map (fun i =>
        mul (directions i) (entropyBitGradient (affineCoordinate (masses i) (directions i) t) (lower i) (hx i).1)))) := by
  let domain := entropyLineDomain masses directions lower
  let functions := fun i t (hx : domain t) => (affineCoordinate (masses i) (directions i) t).realEntropyTerm
    (entropyPositiveNonnegative (lower i) _ (hx i)) (hx i).2
  let slopes := fun i t (hx : domain t) => mul (directions i)
    (entropyBitGradient (affineCoordinate (masses i) (directions i) t) (lower i) (hx i).1)
  let coordinate (i : Fin variables) : UniformDerivativeWithin domain (functions i) (slopes i) :=
    (realEntropyTerm_uniformDerivative (lower i)).affine_pullback (directions i) (masses i) (fun _ hx => hx i)
  exact (UniformDerivativeWithin.listSum (List.finRange variables) functions slopes coordinate).function_congr (fun _ _ => by
    simp only [entropyLine, realEntropySum, List.map_map]
    exact equiv_refl _)

/-- Natural-unit first variation on the entire admitted line, including
its endpoints. The bit-to-natural conversion is proved coordinatewise. -/
def naturalEntropyLine_uniformDerivative (masses directions : Fin variables → ConstructiveReal)
    (lower : Fin variables → PositiveRatio) :
    UniformDerivativeWithin (entropyLineDomain masses directions lower)
      (fun t hx => mul (entropyLine masses directions lower t hx) lnTwo)
      (fun t hx => listSum ((List.finRange variables).map (fun i =>
        mul (directions i) (entropyNaturalGradient (affineCoordinate (masses i) (directions i) t) (lower i) (hx i).1)))) :=
  ((entropyLine_uniformDerivative masses directions lower).mul_constant lnTwo).slope_congr
    (fun t hx => entropyFirstVariation_units _ (fun i => affineCoordinate (masses i) (directions i) t) directions lower (fun i => (hx i).1))

end Thesis.Probability.ConstructiveReal
