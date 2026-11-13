import Thesis.Probability.ConstructiveUniformChain
import Thesis.Probability.ConstructiveUniformAffine
import Thesis.Probability.ConstructiveRealEntropyGradientBounds
import Thesis.Probability.ConstructiveRealEntropyUniformDerivative
import Thesis.Probability.ConstructiveRealFiniteLinear
import Thesis.Probability.ConstructiveDerivativeUniqueness

namespace Thesis.Probability
open ConstructiveReal

/-- Quantitatively regular auxiliary probability coordinates on an explicit
parameter domain. Outside that domain the coordinate functions need not be
probabilities, so affine and nonlinear local paths are both allowed. Their
normalization identity is global, permitting derivative uniqueness at admitted
endpoints without assuming that those endpoints are interior to the domain.
Uniform remainders and velocity bounds are explicit data; entropy derivatives
and tangent equations are conclusions. Rational `Distro` weights are unchanged. -/
structure RegularProbabilityCurve (states : Nat) (domain : ConstructiveReal → Prop) where
  mass : Fin states → ConstructiveReal → ConstructiveReal
  velocity : Fin states → ConstructiveReal → ConstructiveReal
  pointDerivative : ∀ i t, domain t → HasDerivativeAt (mass i) t (velocity i t)
  normalized : ∀ t, Equiv (Distros.RationalLinear.realDot states (fun _ => 1) (fun i => mass i t)) one
  uniformDerivative : ∀ i, UniformDerivativeWithin domain (fun t _ => mass i t) (fun t _ => velocity i t)
  lower : Fin states → PositiveRatio
  positive : ∀ i t, domain t → LE (ofSignedRatio (lower i).toSignedRatio) (mass i t)
  bounded : ∀ i t, domain t → LE (mass i t) one
  velocityLower : Fin states → ConstructiveReal
  velocityUpper : Fin states → ConstructiveReal
  velocityBounds : ∀ i t, domain t → LE (velocityLower i) (velocity i t) ∧ LE (velocity i t) (velocityUpper i)

namespace RegularProbabilityCurve

def inside (curve : RegularProbabilityCurve states domain) (i : Fin states) (t : ConstructiveReal) (admitted : domain t) :
    entropyPositiveDomain (curve.lower i) (curve.mass i t) := ⟨curve.positive i t admitted, curve.bounded i t admitted⟩

def probability (curve : RegularProbabilityCurve states domain) (t : ConstructiveReal) (admitted : domain t) (i : Fin states) : UnitIntervalValue :=
  ⟨curve.mass i t, entropyPositiveNonnegative (curve.lower i) _ (curve.inside i t admitted), curve.bounded i t admitted⟩

def entropy (curve : RegularProbabilityCurve states domain) (t : ConstructiveReal) (admitted : domain t) : ConstructiveReal :=
  realEntropySum ((List.finRange states).map (curve.probability t admitted))

def bitRate (curve : RegularProbabilityCurve states domain) (t : ConstructiveReal) (admitted : domain t) : ConstructiveReal :=
  FiniteLinear.pair states (fun i => curve.velocity i t)
    (fun i => entropyBitGradient (curve.mass i t) (curve.lower i) (curve.positive i t admitted))

def naturalRate (curve : RegularProbabilityCurve states domain) (t : ConstructiveReal) (admitted : domain t) : ConstructiveReal :=
  FiniteLinear.pair states (fun i => curve.velocity i t)
    (fun i => entropyNaturalGradient (curve.mass i t) (curve.lower i) (curve.positive i t admitted))

/-- The actual entropy has a computed uniform derivative along this general
probability curve. The joint modulus is assembled from the coordinate
certificates, uniform signed velocity bounds and the proved entropy-gradient
bounds, rather than assumed as an extra path hypothesis. -/
def entropy_uniformDerivative (curve : RegularProbabilityCurve states domain) :
    UniformDerivativeWithin domain curve.entropy curve.bitRate := by
  let functions := fun i t (admitted : domain t) => (curve.mass i t).realEntropyTerm
    (entropyPositiveNonnegative (curve.lower i) _ (curve.inside i t admitted)) (curve.bounded i t admitted)
  let slopes := fun i t (admitted : domain t) => mul (curve.velocity i t)
    (entropyBitGradient (curve.mass i t) (curve.lower i) (curve.positive i t admitted))
  have coordinate (i : Fin states) : UniformDerivativeWithin domain (functions i) (slopes i) :=
    (curve.uniformDerivative i).chainWithin (realEntropyTerm_uniformDerivative (curve.lower i)) (curve.inside i)
      (intervalMagnitudeBound (curve.velocityLower i) (curve.velocityUpper i)) (entropyGradientMagnitudeBound (curve.lower i))
      (fun t admitted precision fine => magnitude_bounded_of_interval _ _ _
        (curve.velocityBounds i t admitted).1 (curve.velocityBounds i t admitted).2 precision fine)
      (fun x admitted precision fine => entropyBitGradient_magnitude_bounded x (curve.lower i) admitted precision fine)
  exact (UniformDerivativeWithin.listSum (List.finRange states) functions slopes coordinate).function_congr (fun _ _ => by
    simp only [entropy, realEntropySum, List.map_map]
    exact equiv_refl _)

/-- The entire derived first variation is converted to natural units with
the existing proved ln(2) factor. -/
def naturalEntropy_uniformDerivative (curve : RegularProbabilityCurve states domain) :
    UniformDerivativeWithin domain (fun t admitted => mul (curve.entropy t admitted) lnTwo) curve.naturalRate :=
  (curve.entropy_uniformDerivative.mul_constant lnTwo).slope_congr (fun t admitted =>
    entropyFirstVariation_units (List.finRange states) (fun i => curve.mass i t) (fun i => curve.velocity i t)
      curve.lower (fun i => curve.positive i t admitted))

/-- Conservation of probability velocity is derived from the actual global
normalization identity and total point derivatives. An arbitrary derivative
within a possibly isolated domain would not justify this conclusion. -/
theorem normalized_velocity (curve : RegularProbabilityCurve states domain) (point : ConstructiveReal) (admitted : domain point) :
    Equiv (Distros.RationalLinear.realDot states (fun _ => 1) (fun i => curve.velocity i point)) zero := by
  have normalizedSum (t : ConstructiveReal) : Equiv (listSum ((List.finRange states).map (fun i => curve.mass i t))) one :=
    equiv_trans (equiv_symm (equiv_trans (FiniteLinear.realDot_pair states (fun _ => 1) (fun i => curve.mass i t))
      (listSum_map_congr (List.finRange states) _ _ (fun i _ => one_mul (curve.mass i t))))) (curve.normalized t)
  let summed := HasDerivativeAt.listSum (List.finRange states) curve.mass (fun i => curve.velocity i point) point
    (fun i => curve.pointDerivative i point admitted)
  have vanished := (summed.function_congr normalizedSum).unique (HasDerivativeAt.constant point one)
  exact equiv_trans (equiv_trans (FiniteLinear.realDot_pair states (fun _ => 1) (fun i => curve.velocity i point))
    (listSum_map_congr (List.finRange states) _ _ (fun i _ => one_mul _))) vanished

end RegularProbabilityCurve
end Thesis.Probability
