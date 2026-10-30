import Thesis.Probability.ConstructiveProbabilityCurve
import Thesis.Probability.FiniteGibbsEntropyVariation

namespace Thesis.Probability.RegularProbabilityCurve
open ConstructiveReal

/-- The actual entropy rate along any regular probability curve of Gibbs
laws. Both the family and its parameter may vary. Normalization supplies the
tangent equation; positive logarithm floors are transferred from the curve
and the current normalized Gibbs law. No affine-path assumption is used. -/
theorem gibbs_naturalRate (curve : RegularProbabilityCurve states domain)
    (family : ∀ t, domain t → FiniteGibbsTilt states) (parameter : ∀ t, domain t → ConstructiveReal)
    (atGibbs : ∀ t hx i, Equiv (curve.mass i t) ((family t hx).mass (parameter t hx) i))
    (t : ConstructiveReal) (admitted : domain t) :
    Equiv (curve.naturalRate t admitted)
      (sub (mul (parameter t admitted) (FiniteLinear.pair states (fun i => curve.velocity i t) (family t admitted).energy))
        (FiniteLinear.pair states (fun i => curve.velocity i t) (family t admitted).offset)) := by
  have gradients (i : Fin states) : Equiv
      (entropyNaturalGradient (curve.mass i t) (curve.lower i) (curve.positive i t admitted))
      (entropyNaturalGradient ((family t admitted).mass (parameter t admitted) i)
        ((family t admitted).massLower (parameter t admitted) i) ((family t admitted).mass_positive (parameter t admitted) i)) :=
    neg_congr (add_congr (positiveLn_congr (atGibbs t admitted i) _ _ (curve.positive i t admitted)
      ((family t admitted).mass_positive (parameter t admitted) i)) (equiv_refl one))
  exact equiv_trans (FiniteLinear.pair_congr states _ _ _ _ (fun _ => equiv_refl _) gradients)
    ((family t admitted).naturalGradient_pair (parameter t admitted) (fun i => curve.velocity i t) (curve.normalized_velocity t admitted))

/-- Uniform quantitative Gibbs entropy variation along a general admitted
curve. Its modulus comes from the actual probability-coordinate certificates,
not from separately assuming a uniform entropy or Clausius certificate. -/
def gibbsEntropy_uniformDerivative (curve : RegularProbabilityCurve states domain)
    (family : ∀ t, domain t → FiniteGibbsTilt states) (parameter : ∀ t, domain t → ConstructiveReal)
    (atGibbs : ∀ t hx i, Equiv (curve.mass i t) ((family t hx).mass (parameter t hx) i)) :
    UniformDerivativeWithin domain (fun t hx => mul (curve.entropy t hx) lnTwo)
      (fun t hx => sub (mul (parameter t hx) (FiniteLinear.pair states (fun i => curve.velocity i t) (family t hx).energy))
        (FiniteLinear.pair states (fun i => curve.velocity i t) (family t hx).offset)) :=
  curve.naturalEntropy_uniformDerivative.slope_congr (curve.gibbs_naturalRate family parameter atGibbs)

end Thesis.Probability.RegularProbabilityCurve
