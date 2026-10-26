import Thesis.Probability.ConstructiveRealEntropyOptimizer
import Thesis.Examples.EntropyMeanHalf

namespace Thesis.Examples.ConstructiveEntropyOptimizer
open Probability Probability.Distros ConstructiveReal

/-- The existing mean-half example now has an attained ideal optimum,
without claiming that its three probability values are rational. -/
def meanHalfIdeal : EntropyMeanHalf.problem.RealCompatibleLaw :=
  EntropyMeanHalf.problem.idealEntropyLaw EntropyMeanHalf.anchor

/-- The original rational certificate encloses the attained ideal entropy,
not merely an unattained rational supremum or a finite candidate search. -/
example : LE (ofSignedRatio (⟨2599, 2000, by decide⟩ : QProb).toSignedRatio) meanHalfIdeal.entropy ∧
    LE meanHalfIdeal.entropy (ofSignedRatio (⟨2601, 2000, by decide⟩ : QProb).toSignedRatio) := by
  have lower := ExactLog.interpret_mono EntropyMeanHalf.certificate.lower_bound
  have interpreted : LE (ofSignedRatio EntropyMeanHalf.certificate.lower.toSignedRatio) EntropyMeanHalf.anchor.toReal.entropy :=
    (le_congr (ExactLog.interpret_ofSignedRatio _) (equiv_symm EntropyMeanHalf.anchor.toReal_entropy)).mp lower
  exact ⟨le_trans interpreted (EntropyMeanHalf.problem.idealEntropyLaw_maximal EntropyMeanHalf.anchor _),
    EntropyMeanHalf.certificate.real_global_bound meanHalfIdeal⟩

/-- Redundant exact rows and the noncanonical rational anchor do not affect
the uniquely attained probabilities. -/
example (other : EntropyMeanHalf.problem.RealCompatibleLaw) (maximal : other.Maximal)
    (index : Fin EntropyMeanHalf.problem.cells.length) :
    Equiv (other.mass index).value (meanHalfIdeal.mass index).value :=
  other.maximal_unique meanHalfIdeal maximal
    (EntropyMeanHalf.problem.idealEntropyLaw_maximal EntropyMeanHalf.anchor) index

example (radius : PositiveRatio) (n : Nat)
    (later : radius.half.half.entropyGapPrecision.den ≤ n) (index : Fin EntropyMeanHalf.problem.cells.length) :
    Within radius.toQProb
      ((EntropyMeanHalf.problem.entropyApproximations EntropyMeanHalf.anchor n).law.toReal.mass index).value
      (meanHalfIdeal.mass index).value :=
  EntropyMeanHalf.problem.idealEntropyLaw_coordinate_converges EntropyMeanHalf.anchor radius n later index

private def zeroSecond : MomentInterval Nat := MomentInterval.exact (fun value => if value = 1 then 1 else 0) SignedRatio.zero
private def redundant : MomentInterval Nat := MomentInterval.exact (fun _ => -2) ⟨-2, 1, by decide⟩
private def boundary : PartialMomentProblem Nat :=
  ⟨[0, 1], 0, by decide, by decide, [zeroSecond, redundant, redundant]⟩
private def point : Distro Nat := ⟨⟨[(0, 3), (1, 0), (77, 0)], 3, by decide, by decide⟩⟩
private def anchor : boundary.CompatibleLaw := ⟨point, (by
  change ∀ atom ∈ point.record.atoms, 0 < atom.2 → atom.1 ∈ boundary.cells
  decide +kernel), (by
  intro row member
  change row ∈ [zeroSecond, redundant, redundant] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨by decide +kernel, by decide +kernel⟩), (by
  intro cell member
  change cell ∈ [0, 1] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨3, by decide⟩
  · exact ⟨0, by decide⟩)⟩

private theorem boundary_zero (law : boundary.RealCompatibleLaw) :
    Equiv (law.mass ⟨1, by decide⟩).value zero := by
  have member : (⟨zeroSecond.coefficients boundary.cells boundary.default, SignedRatio.zero⟩ : RationalLinear.Inequality 2) ∈ boundary.rows := by
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨zeroSecond, List.mem_cons_self .., List.mem_cons_self ..⟩)
  have original := law.valid _ member
  have coefficients : zeroSecond.coefficients boundary.cells boundary.default = (fun i : Fin 2 => if i = 1 then 1 else 0) := by
    funext i
    change Fin 2 at i
    have alternatives : i = 0 ∨ i = 1 := by
      have bound := i.isLt
      by_cases h : i.val = 0
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by omega))
    rcases alternatives with rfl | rfl <;> decide +kernel
  change LE (RationalLinear.realDot 2 (zeroSecond.coefficients boundary.cells boundary.default) (fun i => (law.mass i).value)) zero at original
  rw [coefficients] at original
  exact ⟨(le_congr (RationalLinear.realDot_unit 2 1 _) (equiv_refl _)).mp original, (law.mass ⟨1, by decide⟩).nonnegative⟩

/-- The constructed ideal optimizer keeps the forced-zero coordinate
exactly zero, despite repeated signed constraints and a retained null outlier
in the rational anchor. No strictly positive feasible point is assumed. -/
example : Equiv ((boundary.idealEntropyLaw anchor).mass ⟨1, by decide⟩).value zero :=
  boundary_zero (boundary.idealEntropyLaw anchor)

/-- The quantitative gap-to-radius conversion is concrete: two entropy
gaps of 1/800 suffice for coordinate error 1/10. -/
example : QProb.LE (QProb.mul (QProb.ofNat 4) (QProb.add ⟨1, 800, by decide⟩ ⟨1, 800, by decide⟩))
    (QProb.mul (⟨1, 10, by decide⟩ : QProb) ⟨1, 10, by decide⟩) := by decide +kernel

end Thesis.Examples.ConstructiveEntropyOptimizer
