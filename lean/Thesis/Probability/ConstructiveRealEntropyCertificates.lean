import Thesis.Probability.ConstructiveRealMomentApproximation
import Thesis.Probability.Distros.EntropyOptimize

namespace Thesis.Probability.Distros.PartialMomentProblem
open ConstructiveReal

private theorem constant_error_sum (values : List A) (error : QProb) :
    QProb.Equiv (QProb.listSum (values.map (fun _ => error))) (QProb.mul error (QProb.ofNat values.length)) := by
  induction values with
  | nil =>
      simp only [List.map_nil, QProb.listSum, QProb.Equiv, QProb.zero, QProb.mul, QProb.ofNat, List.length_nil, Nat.zero_mul, Nat.mul_zero]
  | cons value rest ih =>
      apply QProb.equiv_trans (QProb.add_congr (QProb.equiv_refl error) ih)
      simp only [QProb.Equiv, QProb.add, QProb.mul, QProb.ofNat, List.length_cons, Nat.mul_one,
        Nat.mul_add, Nat.add_mul]
      ac_rfl

/-- A computed coordinate precision suffices for any requested entropy
accuracy; the finite coordinate errors receive equal shares. -/
def RealCompatibleLaw.entropyInput {problem : PartialMomentProblem A} (_law : problem.RealCompatibleLaw)
    (precision : PositiveRatio) : PositiveRatio :=
  (entropyInputPrecision (precision.divideNat problem.cells.length problem.nonempty)).half

/-- Finite ideal entropy has a computed uniform continuity modulus on
the feasible polytope, including every boundary coordinate. -/
theorem RealCompatibleLaw.entropy_within {problem : PartialMomentProblem A}
    (law other : problem.RealCompatibleLaw) (precision : PositiveRatio)
    (close : ∀ i, Within (law.entropyInput precision).toQProb (law.mass i).value (other.mass i).value) :
    Within precision.toQProb law.entropy other.entropy := by
  let perCoordinate := precision.divideNat problem.cells.length problem.nonempty
  let indices := List.finRange problem.cells.length
  have coordinate (i : Fin problem.cells.length) : Within perCoordinate.toQProb (law.mass i).entropy (other.mass i).entropy :=
    realEntropyTerm_within (law.mass i).value (other.mass i).value
      (law.mass i).nonnegative (other.mass i).nonnegative (law.mass i).bounded (other.mass i).bounded perCoordinate (close i)
  have compared : Within (QProb.listSum (indices.map (fun _ => perCoordinate.toQProb))) law.entropy other.entropy := by
    simp only [RealCompatibleLaw.entropy, realEntropySum, List.map_map]
    exact within_listSum_map indices _ _ _ (fun i _ => coordinate i)
  have collected : QProb.Equiv (QProb.listSum (indices.map (fun _ => perCoordinate.toQProb))) precision.toQProb :=
    QProb.equiv_trans (constant_error_sum indices perCoordinate.toQProb)
      (by simpa only [indices, List.length_finRange] using PositiveRatio.divide_mul precision problem.cells.length problem.nonempty)
  exact within_mono compared (QProb.le_congr (QProb.equiv_refl _) collected (QProb.le_refl _))

/-- Effective density also holds in entropy value, with every approximating
law satisfying the original rational constraints exactly. This is stronger
than merely approximating each coordinate without preserving normalization. -/
def RealCompatibleLaw.approximateEntropy [DecidableEq A] {problem : PartialMomentProblem A}
    (law : problem.RealCompatibleLaw) (precision : PositiveRatio) :
    {rational : problem.CompatibleLaw // Within precision.toQProb law.entropy
      (rational.distro.entropy problem.entropyGrid rational.support).interpret} := by
  let approximation := law.approximate (law.entropyInput precision)
  let rational := approximation.val
  have compared : Within precision.toQProb law.entropy rational.toReal.entropy :=
    law.entropy_within rational.toReal precision approximation.property
  exact ⟨rational, (within_congr (error := precision.toQProb) (equiv_refl law.entropy) rational.toReal_entropy).mp compared⟩

/-- A universal exact rational entropy certificate bounds every feasible
auxiliary real law. Exactly feasible density and closed real order discharge
the transfer; no irrational candidate is smuggled into the rational solver. -/
theorem EntropyCertificate.real_global_bound [DecidableEq A] {problem : PartialMomentProblem A} {tolerance : QProb}
    (certificate : problem.EntropyCertificate tolerance) (law : problem.RealCompatibleLaw) :
    LE law.entropy (ofSignedRatio certificate.upper.toSignedRatio) := by
  apply le_of_forall_rational_error
  intro precision
  let approximation := law.approximateEntropy precision
  let rational := approximation.val
  have bounded : LE (rational.distro.entropy problem.entropyGrid rational.support).interpret
      (ofSignedRatio certificate.upper.toSignedRatio) :=
    (le_congr (equiv_refl _) (ExactLog.interpret_ofSignedRatio certificate.upper.toSignedRatio)).mp
      (ExactLog.interpret_mono (certificate.global_bound rational.distro ⟨rational.support, rational.moments⟩))
  exact le_trans approximation.property.1 (add_le_add bounded (le_refl _))

end Thesis.Probability.Distros.PartialMomentProblem
