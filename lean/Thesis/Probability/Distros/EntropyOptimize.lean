import Thesis.Probability.Distros.EntropyBoxSearch
import Thesis.Probability.ExactLogPositiveEnclosure

namespace Thesis.Probability.QProb

/-- A witnessed nonnegative difference inherits the corresponding additive
upper bound, without introducing signed probability weights. -/
theorem sub_le_of_le_add (p q r : QProb) (ordered : LE q p) (bounded : LE p (add q r)) :
    LE (sub p q ordered) r := by
  have cleared : (p.num * q.den) * r.den ≤ (q.num * p.den) * r.den + r.num * (p.den * q.den) := by
    simpa only [LE, add, Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bounded
  change (p.num * q.den - q.num * p.den) * r.den ≤ r.num * (p.den * q.den)
  rw [Nat.sub_mul]
  omega

end Thesis.Probability.QProb

namespace Thesis.Probability.Distros.PartialMomentProblem

/-- An exactly feasible rational law with a global rational entropy bracket.
`gap` states `U ≤ L + epsilon`, so no signed atom weights are introduced. -/
structure EntropyCertificate [DecidableEq A] (problem : PartialMomentProblem A) (tolerance : QProb) where
  law : problem.CompatibleLaw
  lower : QProb
  upper : QProb
  lower_bound : ExactLog.LE (ExactLog.ofQProb lower) (law.distro.entropy problem.entropyGrid law.support)
  global_bound : ∀ μ (valid : problem.Admissible μ),
    ExactLog.LE (μ.entropy problem.entropyGrid valid.1) (ExactLog.ofQProb upper)
  gap : QProb.LE upper (QProb.add lower tolerance)

/-- The returned interval is ordered; applying the universal bound to the
returned exactly feasible law gives `L ≤ H(q) ≤ U`. -/
theorem EntropyCertificate.lower_le_upper [DecidableEq A] {problem : PartialMomentProblem A} {tolerance : QProb}
    (certificate : problem.EntropyCertificate tolerance) : QProb.LE certificate.lower certificate.upper :=
  (ExactLog.ofQProb_le_iff _ _).mp (ExactLog.le_trans certificate.lower_bound
    (certificate.global_bound certificate.law.distro ⟨certificate.law.support, certificate.law.moments⟩))

/-- The additive gap field is exactly the requested witnessed difference
bound `U - L ≤ epsilon` in the existing nonnegative rational interface. -/
theorem EntropyCertificate.width_bound [DecidableEq A] {problem : PartialMomentProblem A} {tolerance : QProb}
    (certificate : problem.EntropyCertificate tolerance) :
    QProb.LE (QProb.sub certificate.upper certificate.lower certificate.lower_le_upper) tolerance :=
  QProb.sub_le_of_le_add _ _ _ certificate.lower_le_upper certificate.gap

/-- Rational enclosure width and symbolic optimization error each receive
half of the supplied epsilon. The resulting bounds cover all feasible laws. -/
def certifyEntropy [DecidableEq A] (problem : PartialMomentProblem A) (initial : problem.CompatibleLaw)
    (tolerance : QProb) (positive : 0 < tolerance.num) : problem.EntropyCertificate tolerance := by
  let half : QProb := ⟨tolerance.num, 2 * tolerance.den, Nat.mul_pos (by decide) tolerance.den_pos⟩
  let approximation := problem.approximateEntropy initial half positive
  let law := approximation.law
  let enclosed := ExactLog.encloseNonnegative (law.distro.entropy problem.entropyGrid law.support)
    (law.distro.entropy_nonnegative problem.entropyGrid law.support) half positive
  let upper := QProb.add enclosed.upper half
  have halves : QProb.Equiv (QProb.add half half) tolerance := by
    refine QProb.equiv_trans (QProb.add_mk_same_den (2 * tolerance.den)
      (Nat.mul_pos (by decide) tolerance.den_pos) tolerance.num tolerance.num) ?_
    simp only [QProb.Equiv, Nat.add_mul, Nat.two_mul, Nat.mul_add]
  refine ⟨law, enclosed.lower, upper, enclosed.lower_bound, ?_, ?_⟩
  · intro μ valid
    change ExactLog.LE (μ.entropy problem.entropyGrid valid.1) (ExactLog.ofQProb (QProb.add enclosed.upper half))
    rw [← ExactLog.ofQProb_add]
    exact ExactLog.le_trans (approximation.upper μ valid)
      ((ExactLog.add_le_add_right_iff _ _ (ExactLog.ofQProb half)).mpr enclosed.upper_bound)
  · have first := QProb.add_le_add enclosed.width_bound (QProb.le_refl half)
    have endpoints := QProb.equiv_trans (QProb.add_assoc enclosed.lower half half)
      (QProb.add_congr (QProb.equiv_refl _) halves)
    exact QProb.le_congr (QProb.equiv_refl _) endpoints first

/-- The original constructive infeasibility certificate is retained. -/
inductive EntropyResult [DecidableEq A] (problem : PartialMomentProblem A) (tolerance : QProb) where
  | feasible : problem.EntropyCertificate tolerance → EntropyResult problem tolerance
  | infeasible : RationalLinear.Infeasibility problem.cells.length problem.rows → EntropyResult problem tolerance

/-- Total certified maximum-entropy approximation for rational moment
problems at every positive rational tolerance. No denominator cap is imposed
on feasible laws or solver witnesses. The fallback finite cover is a complete
reference algorithm and may be expensive to enumerate. -/
def solveEntropy [DecidableEq A] (problem : PartialMomentProblem A) (tolerance : QProb)
    (positive : 0 < tolerance.num) : problem.EntropyResult tolerance :=
  match problem.solve with
  | .feasible initial => .feasible (problem.certifyEntropy initial tolerance positive)
  | .infeasible certificate => .infeasible certificate

end Thesis.Probability.Distros.PartialMomentProblem
