import Thesis.Probability.ConstructiveRealEntropyCertificates
import Thesis.Examples.EntropyMeanHalf

namespace Thesis.Examples.ConstructiveRealFeasibility
open Probability Probability.Distros ConstructiveReal

private def zeroSecond : RationalLinear.Inequality 2 := ⟨fun i => if i = 1 then 1 else 0, SignedRatio.zero⟩
private def repeated : RationalLinear.Inequality 2 := ⟨fun _ => 3, ⟨3, 1, by decide⟩⟩
private def upperBand : RationalLinear.Inequality 2 := ⟨fun i => if i = 0 then 1 else -1, SignedRatio.one⟩
private def lowerBand : RationalLinear.Inequality 2 := ⟨fun i => if i = 0 then -1 else 1, SignedRatio.zero⟩

/-- The simplex, an exact forced zero, a closed signed interval, and a
repeated redundant row all enter the original solver together. -/
private def rows : List (RationalLinear.Inequality 2) :=
  RationalLinear.simplexRows 2 ++ [zeroSecond, upperBand, lowerBand, repeated, repeated]
private def vector : Fin 2 → SignedRatio := fun i => if i = 0 then SignedRatio.one else SignedRatio.zero
private theorem vector_valid : RationalLinear.Satisfies rows vector := by decide +kernel
private theorem real_valid : RationalLinear.RealSatisfies rows (fun i => ofSignedRatio (vector i)) := by
  intro row member
  exact (le_congr (RationalLinear.realDot_ofSignedRatio 2 row.coefficients vector) (equiv_refl _)).mpr
    ((ofSignedRatio_le_iff _ _).mpr (vector_valid row member))

private theorem forced_zero (rational : Fin 2 → SignedRatio) (valid : RationalLinear.Satisfies rows rational) :
    SignedRatio.Equiv (rational 1) SignedRatio.zero := by
  have simplex := (RationalLinear.satisfies_simplex_iff 2 rational).mp
    (fun row member => valid row (List.mem_append_left _ member))
  have lower : SignedRatio.LE SignedRatio.zero (rational 1) :=
    (SignedRatio.zero_le_iff_nonnegative _).mpr (simplex.1 1)
  have original := valid zeroSecond (List.mem_append_right _ (List.mem_cons_self ..))
  have upper : SignedRatio.LE (rational 1) SignedRatio.zero :=
    (SignedRatio.le_congr (RationalLinear.dot_unit 2 1 rational) (SignedRatio.equiv_refl _)).mp original
  exact SignedRatio.equiv_of_le_of_le upper lower

/-- At every requested precision, the returned rational point has exactly
zero second coordinate. This follows from the unchanged constraints, rather
than an approximation error bound that could merely make it small. -/
example (precision : PositiveRatio) : SignedRatio.Equiv
    ((RationalLinear.approximateFeasible rows (fun i => ofSignedRatio (vector i)) real_valid precision).val 1) SignedRatio.zero :=
  forced_zero _ (RationalLinear.approximateFeasible rows (fun i => ofSignedRatio (vector i)) real_valid precision).property.1

/-- The previously certified three-state mean-half upper bound now covers
all feasible real laws, including any irrational ideal optimizer when its
existence is established. It is not restricted to rational competitors. -/
example (law : EntropyMeanHalf.problem.RealCompatibleLaw) :
    LE law.entropy (ofSignedRatio (⟨2601, 2000, by decide⟩ : QProb).toSignedRatio) :=
  EntropyMeanHalf.certificate.real_global_bound law

/-- This anchor has a split observable atom and a null outlier. The ideal
law reads its aggregated PMFs, not entropy of the raw record occurrences. -/
example : Equiv EntropyMeanHalf.anchor.toReal.entropy
    (EntropyMeanHalf.anchor.distro.entropy EntropyMeanHalf.problem.entropyGrid EntropyMeanHalf.anchor.support).interpret :=
  EntropyMeanHalf.anchor.toReal_entropy

end Thesis.Examples.ConstructiveRealFeasibility
