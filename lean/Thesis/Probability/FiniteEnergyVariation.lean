import Thesis.Probability.ConstructiveDerivativeProduct
import Thesis.Probability.ConstructiveRealBilinearFubini

namespace Thesis.Probability.ConstructiveReal.FiniteLinear
open ConstructiveReal

private theorem sum_add (indices : List A) (first second : A → ConstructiveReal) :
    Equiv (listSum (indices.map (fun i => add (first i) (second i))))
      (add (listSum (indices.map first)) (listSum (indices.map second))) := by
  induction indices with
  | nil => exact equiv_symm (zero_add zero)
  | cons i rest ih => exact equiv_trans (add_congr (equiv_refl _) ih) (add_four _ _ _ _)

/-- Differentiate the actual finite bilinear pairing by the product rule.
Both factors may vary; all effective remainders are retained. -/
def pair_hasDerivativeAt (first second : Fin size → ConstructiveReal → ConstructiveReal)
    (point : ConstructiveReal) (firstSlope secondSlope : Fin size → ConstructiveReal)
    (firstDerivative : ∀ i, HasDerivativeAt (first i) point (firstSlope i))
    (secondDerivative : ∀ i, HasDerivativeAt (second i) point (secondSlope i)) :
    HasDerivativeAt (fun t => pair size (fun i => first i t) (fun i => second i t)) point
      (add (pair size firstSlope (fun i => second i point)) (pair size (fun i => first i point) secondSlope)) :=
  (HasDerivativeAt.listSum (List.finRange size) (fun i t => mul (first i t) (second i t))
    (fun i => add (mul (firstSlope i) (second i point)) (mul (first i point) (secondSlope i))) point
    (fun i => (firstDerivative i).mul (secondDerivative i))).slope_congr (sum_add _ _ _)

end Thesis.Probability.ConstructiveReal.FiniteLinear

namespace Thesis.Probability.FiniteEnergyVariation
open ConstructiveReal

/-- Mean energy, with both the probabilities and the energy levels allowed
to vary. Application as a physical expectation separately requires a
normalized nonnegative probability path. -/
def meanEnergy (probability levels : Fin states → ConstructiveReal → ConstructiveReal) (t : ConstructiveReal) : ConstructiveReal :=
  FiniteLinear.pair states (fun i => probability i t) (fun i => levels i t)

/-- Probability contribution to energy. In a closed system this is the
thermal heat rate; in an open system chemical exchange must be subtracted
as in `FiniteStatisticalMechanics.grandCanonical_clausius`. -/
def heatRate (velocity levels : Fin states → ConstructiveReal) : ConstructiveReal := FiniteLinear.pair states velocity levels
def workRate (probability levelVelocity : Fin states → ConstructiveReal) : ConstructiveReal := FiniteLinear.pair states probability levelVelocity

/-- The finite first-law decomposition is a proved product derivative:
changes in probabilities contribute the probability energy term and changes
in levels contribute work. Interpreting the first term as thermal heat
requires a closed system or a separate chemical-exchange correction. No
physical adequacy or equilibrium of a path is postulated. -/
def meanEnergy_hasDerivativeAt (probability levels : Fin states → ConstructiveReal → ConstructiveReal)
    (point : ConstructiveReal) (velocity levelVelocity : Fin states → ConstructiveReal)
    (probabilityDerivative : ∀ i, HasDerivativeAt (probability i) point (velocity i))
    (levelDerivative : ∀ i, HasDerivativeAt (levels i) point (levelVelocity i)) :
    HasDerivativeAt (meanEnergy probability levels) point
      (add (heatRate velocity (fun i => levels i point)) (workRate (fun i => probability i point) levelVelocity)) :=
  FiniteLinear.pair_hasDerivativeAt probability levels point velocity levelVelocity probabilityDerivative levelDerivative

end Thesis.Probability.FiniteEnergyVariation
