import Thesis.Probability.ConstructiveRealRationalEntropyOptimizer

namespace Thesis.Examples.RationalEntropyOptimizer
open Probability Probability.Distros ConstructiveReal
open RationalLinear

private def upper : RationalConstraint 3 :=
  ⟨fun i => if i = 0 then ⟨2, 6, by decide⟩ else SignedRatio.zero, ⟨1, 9, by decide⟩⟩
private def lower : RationalConstraint 3 :=
  ⟨fun i => if i = 0 then ⟨-3, 9, by decide⟩ else SignedRatio.zero, ⟨-1, 9, by decide⟩⟩
private def zeroLast : RationalConstraint 3 :=
  ⟨fun i => if i = 2 then ⟨5, 10, by decide⟩ else SignedRatio.zero, SignedRatio.zero⟩
private def band : RationalConstraint 3 :=
  ⟨fun i => if i = 0 then ⟨-2, 7, by decide⟩ else if i = 1 then ⟨3, 14, by decide⟩ else SignedRatio.zero,
    ⟨1, 10, by decide⟩⟩
private def lowerBand : RationalConstraint 3 :=
  ⟨fun i => SignedRatio.neg (band.coefficients i), SignedRatio.zero⟩
private def redundant : RationalConstraint 3 := ⟨fun _ => ⟨4, 12, by decide⟩, ⟨1, 3, by decide⟩⟩

/-- Unreduced signed coefficients, an exact rational equality, a closed
signed band, a forced zero and repeated redundant constraints coexist. -/
private def problem : RationalEntropyProblem 3 :=
  ⟨by decide, [upper, lower, zeroLast, band, lowerBand, redundant, redundant]⟩
private def vector : Fin 3 → SignedRatio :=
  fun i => if i = 0 then ⟨1, 3, by decide⟩ else if i = 1 then ⟨2, 3, by decide⟩ else ⟨0, 11, by decide⟩
/-- Its body is checked below; opacity keeps symbolic optimizer checks from
evaluating the exhaustive reference algorithm during type comparison. -/
private opaque anchor : problem.RealLaw :=
  .ofRationalVector problem vector ⟨by decide +kernel, by decide +kernel⟩ (by decide +kernel)

/-- The feasible witness is supplied constructively, rather than postulating
that a maximizer or a positive point on the full grid already exists. -/
example : anchor.maximize.Maximal := anchor.maximize_maximal

example (other : problem.RealLaw) (maximal : other.Maximal) (index : Fin 3) :
    Equiv (other.mass index).value (anchor.maximize.mass index).value :=
  other.maximal_unique anchor.maximize maximal anchor.maximize_maximal index

/-- The finite dimension transport returns actual original state labels. -/
example (index : Fin 3) : problem.encoded.cells.getD (problem.lawIndex index).val problem.encoded.default = index :=
  (problem.grid_cell (problem.lawIndex index)).trans (problem.gridIndex_lawIndex index)

private theorem forced_zero (law : problem.RealLaw) : Equiv (law.mass 2).value zero := by
  have original := (zeroLast.clear_real_iff (fun i => (law.mass i).value)).mpr
    (law.valid zeroLast (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have coefficients : zeroLast.clear.coefficients = (fun i : Fin 3 => 5 * (if i = 2 then 1 else 0)) := by
    funext i
    have cases' : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      by_cases first : i.val = 0
      · exact Or.inl (Fin.ext first)
      · by_cases second : i.val = 1
        · exact Or.inr (Or.inl (Fin.ext second))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
    rcases cases' with rfl | rfl | rfl <;> decide +kernel
  change LE (realDot 3 zeroLast.clear.coefficients (fun i => (law.mass i).value)) (ofSignedRatio zeroLast.clear.bound) at original
  rw [coefficients] at original
  have dotSame := equiv_trans (realDot_scale_coefficients 3 5 (fun i : Fin 3 => if i = 2 then 1 else 0)
    (fun i => (law.mass i).value)) (mul_congr (equiv_refl _) (realDot_unit 3 2 (fun i => (law.mass i).value)))
  have boundZero : Equiv (ofSignedRatio zeroLast.clear.bound) zero := (ofSignedRatio_equiv_iff _ _).mpr (by decide +kernel)
  have productUpper : LE (mul (realInteger 5) (law.mass 2).value) (mul (realInteger 5) zero) :=
    (le_congr dotSame (equiv_trans boundZero (equiv_symm (mul_zero _)))).mp original
  have upperZero := (mul_le_mul_positive_iff (realInteger 5) (⟨5, 1, by decide, by decide⟩ : PositiveRatio)
    (le_refl _) _ _).mp productUpper
  exact ⟨upperZero, (law.mass 2).nonnegative⟩

/-- The ideal optimum remains exactly on the required boundary face. -/
example : Equiv (anchor.maximize.mass 2).value zero := forced_zero anchor.maximize

private theorem rational_forced_zero (law : problem.encoded.CompatibleLaw) : QProb.Equiv (law.distro.pmf 2) QProb.zero := by
  have zeroValue := forced_zero (RationalEntropyProblem.RealLaw.ofEncoded law.toReal)
  change Equiv (law.toReal.mass (problem.lawIndex 2)).value zero at zeroValue
  rw [problem.encoded_mass] at zeroValue
  exact (QProb.toSignedRatio_equiv_iff _ _).mp ((ofSignedRatio_equiv_iff _ _).mp zeroValue)

/-- Every rational output has an exact zero, not merely a small residual. -/
example (n : Nat) : QProb.Equiv ((anchor.rationalLaw n).pmf 2) QProb.zero := by
  simpa only [RationalEntropyProblem.RealLaw.rationalLaw] using
    (rational_forced_zero (anchor.rationalApproximations n).law)

example (precision : PositiveRatio) :
    ∀ row ∈ problem.rows, row.Holds (fun i => ((anchor.approximate precision).val.pmf i).toSignedRatio) :=
  (anchor.approximate precision).property.1

example (n : Nat) : ∃ weight, ((2 : Fin 3), weight) ∈ (anchor.rationalLaw n).record.atoms :=
  anchor.rationalLaw_retains n 2

example (radius : PositiveRatio) (n : Nat) (later : radius.half.half.entropyGapPrecision.den ≤ n) (index : Fin 3) :
    Within radius.toQProb (ofSignedRatio ((anchor.rationalLaw n).pmf index).toSignedRatio)
      (anchor.maximize.mass index).value := anchor.rationalLaw_converges radius n later index

/-- A universal rational certificate also bounds the attained ideal optimum
for the original signed rational constraints. -/
example (tolerance : QProb) (certificate : problem.encoded.EntropyCertificate tolerance) :
    LE anchor.maximize.entropy (ofSignedRatio certificate.upper.toSignedRatio) :=
  RationalEntropyProblem.certificate_global_bound certificate anchor.maximize

end Thesis.Examples.RationalEntropyOptimizer
