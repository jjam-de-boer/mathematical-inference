import Thesis.Probability.ConstructiveRealGibbsTiltComparison
import Thesis.Probability.ConstructiveRealEqualityConstraints

namespace Thesis.Probability
open ConstructiveReal
open Distros.RationalLinear

/-- A finite multivariate exponential family with original rational features
and positive rational reference weights. Reference weights can encode
physical degeneracies after aggregation; distinct microstate indices are
still distinct states. Parameters and normalized ideal masses are auxiliary
analytic values, with certified rational evaluations. -/
structure FiniteGibbsFamily (states features : Nat) where
  nonempty : 0 < states
  reference : Fin states → PositiveRatio
  response : Fin features → Fin states → SignedRatio

namespace FiniteGibbsFamily

def logReference (family : FiniteGibbsFamily states features) (i : Fin states) : ConstructiveReal :=
  (ofSignedRatio (family.reference i).toSignedRatio).positiveLn (family.reference i) (le_refl _)

def score (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) (i : Fin states) : ConstructiveReal :=
  realRationalDot features (fun j => family.response j i) parameters

def asTilt (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) : FiniteGibbsTilt states :=
  ⟨family.nonempty, family.logReference, family.score parameters⟩

def partition (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) : ConstructiveReal :=
  (family.asTilt parameters).partition one

def logPartition (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) : ConstructiveReal :=
  (family.asTilt parameters).logPartition one

def mass (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) (i : Fin states) : ConstructiveReal :=
  (family.asTilt parameters).mass one i

def probability (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) (i : Fin states) : UnitIntervalValue :=
  (family.asTilt parameters).probability one i

def expectation (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal)
    (observable : Fin states → ConstructiveReal) : ConstructiveReal := (family.asTilt parameters).expectation one observable

def covariance (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal)
    (first second : Fin states → ConstructiveReal) : ConstructiveReal := (family.asTilt parameters).covariance one first second

def entropy (family : FiniteGibbsFamily states features) (parameters : Fin features → ConstructiveReal) : ConstructiveReal :=
  (family.asTilt parameters).entropy one

/-- An affine parameter path. Direction coordinates may be arbitrary signed
analytic values; the feature matrix itself stays rational. -/
def shift (parameters direction : Fin features → ConstructiveReal) (t : ConstructiveReal) (j : Fin features) : ConstructiveReal :=
  affineCoordinate (parameters j) (direction j) t

def along (family : FiniteGibbsFamily states features) (parameters direction : Fin features → ConstructiveReal) : FiniteGibbsTilt states :=
  ⟨family.nonempty, (fun i => sub (family.logReference i) (family.score parameters i)), family.score direction⟩

theorem score_shift (family : FiniteGibbsFamily states features) (parameters direction : Fin features → ConstructiveReal)
    (t : ConstructiveReal) (i : Fin states) :
    Equiv (family.score (shift parameters direction t) i) (add (mul t (family.score direction i)) (family.score parameters i)) :=
  equiv_trans (realRationalDot_pair features (fun j => family.response j i) _)
    (equiv_trans (FiniteLinear.pair_comm features _ _) (equiv_trans (FiniteLinear.pair_add_first features _ _ _)
      (add_congr (equiv_trans (FiniteLinear.pair_scale_first features t direction _)
        (mul_congr (equiv_refl _) (equiv_trans (FiniteLinear.pair_comm features _ _) (equiv_symm (realRationalDot_pair features _ direction)))))
        (equiv_trans (FiniteLinear.pair_comm features _ _) (equiv_symm (realRationalDot_pair features _ parameters))))))

/-- The actual multivariate family along an affine path is exactly the
proved finite tilt. This is the bridge that transfers derivative moduli,
not a formal substitution that assumes multivariate differentiability. -/
theorem along_logWeight (family : FiniteGibbsFamily states features) (parameters direction : Fin features → ConstructiveReal)
    (t : ConstructiveReal) (i : Fin states) :
    Equiv ((family.asTilt (shift parameters direction t)).logWeight one i) ((family.along parameters direction).logWeight t i) :=
  equiv_trans (add_congr (equiv_trans (one_mul _) (neg_congr (family.score_shift parameters direction t i))) (equiv_refl _))
    (equiv_trans (add_congr (neg_add _ _) (equiv_refl _))
      (equiv_trans (add_assoc _ _ _) (add_congr (equiv_symm (mul_neg _ _)) (add_comm _ _))))

theorem along_zero (family : FiniteGibbsFamily states features) (parameters direction : Fin features → ConstructiveReal) (i : Fin states) :
    Equiv ((family.along parameters direction).logWeight zero i) ((family.asTilt parameters).logWeight one i) :=
  equiv_trans (equiv_trans (add_congr (zero_mul _) (equiv_refl _)) (zero_add _))
    (equiv_symm (equiv_trans (add_congr (one_mul _) (equiv_refl _)) (add_comm _ _)))

theorem along_mass (family : FiniteGibbsFamily states features) (parameters direction : Fin features → ConstructiveReal)
    (t : ConstructiveReal) (i : Fin states) :
    Equiv (family.mass (shift parameters direction t) i) ((family.along parameters direction).mass t i) :=
  FiniteGibbsTilt.mass_congr (family.along_logWeight parameters direction t) i

end FiniteGibbsFamily
end Thesis.Probability
