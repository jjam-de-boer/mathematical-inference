import Thesis.Probability.ConstructiveRealEntropyStability

namespace Thesis.Probability.PositiveRatio

/-- Entropy gap sufficient for a requested coordinate radius. -/
def entropyGapPrecision (radius : PositiveRatio) : PositiveRatio :=
  (mul radius radius).divideNat 8 (by decide)

theorem entropyGapPrecision_bound (radius : PositiveRatio) (first second : QProb)
    (left : QProb.LE first radius.entropyGapPrecision.toQProb)
    (right : QProb.LE second radius.entropyGapPrecision.toQProb) :
    QProb.LE (QProb.mul (QProb.ofNat 4) (QProb.add first second)) (QProb.mul radius.toQProb radius.toQProb) := by
  have bounded := QProb.mul_le_mul (QProb.le_refl (QProb.ofNat 4)) (QProb.add_le_add left right)
  have regroup : QProb.Equiv
      (QProb.mul (QProb.ofNat 4) (QProb.add radius.entropyGapPrecision.toQProb radius.entropyGapPrecision.toQProb))
      (QProb.mul radius.entropyGapPrecision.toQProb (QProb.ofNat 8)) := by
    simp only [QProb.Equiv, QProb.mul, QProb.add, QProb.ofNat, Nat.mul_one, Nat.one_mul,
      show (8 : Nat) = 4 + 4 from rfl, Nat.add_mul, Nat.mul_add]
    ac_rfl
  have collect := QProb.equiv_trans regroup (divide_mul (mul radius radius) 8 (by decide))
  exact QProb.le_congr (QProb.equiv_refl _) collect bounded

end Thesis.Probability.PositiveRatio

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal

/-- Coordinate sequence from any supplied family of rational near-maximizers.
Its common modulus is computed from the entropy gaps. Separating the family
from its construction prevents exhaustive solver evaluation inside proofs. -/
def entropyMaximizingCoordinate [DecidableEq A] {problem : PartialMomentProblem A}
    (approximations : (n : Nat) → problem.EntropyApproximation (PositiveRatio.unitPrecision n).toQProb)
    (index : Fin problem.cells.length) : RealCauchySequence where
  value n := (approximations n).law.toReal.mass index |>.value
  modulus radius := radius.entropyGapPrecision.den
  cauchy radius n m left right :=
    ((approximations n).law.toReal).coordinate_within_of_nearOptimal ((approximations m).law.toReal)
      (PositiveRatio.unitPrecision n).toQProb (PositiveRatio.unitPrecision m).toQProb radius
      (approximations n).nearOptimal (approximations m).nearOptimal
      (radius.entropyGapPrecision_bound _ _ (PositiveRatio.unitPrecision_le _ n left)
        (PositiveRatio.unitPrecision_le _ m right)) index

/-- This construction chooses an actual exactly feasible rational law at
every precision. It is total given one initial feasible law; its exhaustive
fallback is a reference algorithm, without an efficiency claim. -/
def entropyApproximations [DecidableEq A] (problem : PartialMomentProblem A) (initial : problem.CompatibleLaw)
    (n : Nat) : problem.EntropyApproximation (PositiveRatio.unitPrecision n).toQProb :=
  problem.approximateEntropy initial (PositiveRatio.unitPrecision n).toQProb (PositiveRatio.unitPrecision n).num_pos

end Thesis.Probability.Distros.PartialMomentProblem
