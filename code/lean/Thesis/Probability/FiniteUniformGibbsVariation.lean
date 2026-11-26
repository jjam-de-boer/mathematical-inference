import Thesis.Probability.ConstructiveUniformEntropyLine
import Thesis.Probability.FiniteGibbsEntropyVariation

/-!
# Uniform natural-entropy variation on a positive affine Gibbs path

The finite affine coordinates are admitted on an explicit positive domain,
have zero total velocity, and agree there with a fixed Gibbs family's
masses at a possibly varying parameter. Scalar entropy remainders first
construct the uniform derivative, then the proved affine Gibbs gradient
rewrites its slope as parameter times energy variation minus offset
variation.

No entropy derivative is supplied as a premise and no uniformity is
deduced from isolated pointwise statements. Positivity, the tangent
equation and the whole-domain Gibbs agreement are explicit data; the
domain may include closed interval endpoints.
-/

namespace Thesis.Probability.FiniteGibbsTilt
open ConstructiveReal

/-- Uniform natural-entropy variation on a supplied positive affine path of
Gibbs laws. The parameter may change along the path. The entropy certificate
is constructed from scalar remainder bounds; only the equilibrium and tangent
equations are supplied. The explicit subdomain can restrict to an interval. -/
def entropyLine_uniformDerivative (family : FiniteGibbsTilt states)
    (masses directions : Fin states → ConstructiveReal) (lower : Fin states → PositiveRatio)
    (domain : ConstructiveReal → Prop)
    (positive : ∀ t, domain t → entropyLineDomain masses directions lower t)
    (tangent : Equiv (Distros.RationalLinear.realDot states (fun _ => 1) directions) zero)
    (parameter : ∀ t, domain t → ConstructiveReal)
    (atGibbs : ∀ t hx i, Equiv (affineCoordinate (masses i) (directions i) t) (family.mass (parameter t hx) i)) :
    UniformDerivativeWithin domain
      (fun t hx => mul (entropyLine masses directions lower t (positive t hx)) lnTwo)
      (fun t hx => sub (mul (parameter t hx) (FiniteLinear.pair states directions family.energy))
        (FiniteLinear.pair states directions family.offset)) :=
  ((naturalEntropyLine_uniformDerivative masses directions lower).restrict domain positive).slope_congr (fun t hx =>
    equiv_trans (listSum_map_congr (List.finRange states) _ _ (fun i _ => mul_congr (equiv_refl _)
      (neg_congr (add_congr (positiveLn_congr (atGibbs t hx i) (lower i) (family.massLower (parameter t hx) i)
        (positive t hx i).1 (family.mass_positive (parameter t hx) i)) (equiv_refl _)))))
      (family.naturalGradient_pair (parameter t hx) directions tangent))

end Thesis.Probability.FiniteGibbsTilt
