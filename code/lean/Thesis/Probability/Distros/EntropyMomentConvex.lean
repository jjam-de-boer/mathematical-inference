import Thesis.Probability.Distros.EntropyConcavity
import Thesis.Probability.Distros.PartialMomentProblem

namespace Thesis.Probability.Distros

/-- Signed rational expectations are affine under the same actual mixture
constructor used by the entropy theorem. All original null atoms remain. -/
theorem Distro.rationalExpectation_mixture_grid [DecidableEq A] (μ ν : Distro A) (grid : EntropyGrid A)
    (first : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (second : ν.AlmostSurely (fun value => value ∈ grid.cells))
    (left right : Nat) (positive : 0 < left + right) (f : A → SignedRatio) :
    SignedRatio.Equiv ((μ.mixture ν left right positive).rationalExpectation f)
      (SignedRatio.add
        (SignedRatio.mul (⟨left, left + right, positive⟩ : QProb).toSignedRatio (μ.rationalExpectation f))
        (SignedRatio.mul (⟨right, left + right, positive⟩ : QProb).toSignedRatio (ν.rationalExpectation f))) := by
  let t := (⟨left, left + right, positive⟩ : QProb).toSignedRatio
  let u := (⟨right, left + right, positive⟩ : QProb).toSignedRatio
  have expanded := (μ.mixture ν left right positive).rationalExpectation_grid_pmf grid.cells grid.distinct
    (μ.mixture_support ν left right positive _ first second) f
  have terms : SignedRatio.Equiv
      (SignedRatio.listSum (grid.cells.map (fun value => SignedRatio.mul ((μ.mixture ν left right positive).pmf value).toSignedRatio (f value))))
      (SignedRatio.listSum (grid.cells.map (fun value => SignedRatio.add
        (SignedRatio.mul t (SignedRatio.mul (μ.pmf value).toSignedRatio (f value)))
        (SignedRatio.mul u (SignedRatio.mul (ν.pmf value).toSignedRatio (f value)))))) := by
    apply SignedRatio.listSum_map_congr
    intro value
    have mass := QProb.toSignedRatio_congr (μ.mixture_pmf ν left right positive value)
    rw [QProb.toSignedRatio_add, QProb.toSignedRatio_mul, QProb.toSignedRatio_mul] at mass
    exact SignedRatio.equiv_trans (SignedRatio.mul_congr mass (SignedRatio.equiv_refl _))
      (SignedRatio.equiv_trans (SignedRatio.add_mul _ _ _)
        (SignedRatio.add_congr (SignedRatio.mul_assoc _ _ _) (SignedRatio.mul_assoc _ _ _)))
  have split := SignedRatio.listSum_map_add grid.cells
    (fun value => SignedRatio.mul t (SignedRatio.mul (μ.pmf value).toSignedRatio (f value)))
    (fun value => SignedRatio.mul u (SignedRatio.mul (ν.pmf value).toSignedRatio (f value)))
  have distributed (ρ : Distro A) (q : SignedRatio) :
      SignedRatio.Equiv (SignedRatio.listSum (grid.cells.map (fun value => SignedRatio.mul q (SignedRatio.mul (ρ.pmf value).toSignedRatio (f value)))))
        (SignedRatio.mul q (SignedRatio.listSum (grid.cells.map (fun value => SignedRatio.mul (ρ.pmf value).toSignedRatio (f value))))) := by
    simpa only [List.map_map, Function.comp_def] using
      SignedRatio.equiv_symm (SignedRatio.mul_listSum q (grid.cells.map (fun value => SignedRatio.mul (ρ.pmf value).toSignedRatio (f value))))
  exact SignedRatio.equiv_trans expanded (SignedRatio.equiv_trans terms (SignedRatio.equiv_trans split
    (SignedRatio.add_congr
      (SignedRatio.equiv_trans (distributed μ t) (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
        (SignedRatio.equiv_symm (μ.rationalExpectation_grid_pmf grid.cells grid.distinct first f))))
      (SignedRatio.equiv_trans (distributed ν u) (SignedRatio.mul_congr (SignedRatio.equiv_refl _)
        (SignedRatio.equiv_symm (ν.rationalExpectation_grid_pmf grid.cells grid.distinct second f)))))))

private theorem signed_constant (left right : Nat) (positive : 0 < left + right) (x : SignedRatio) :
    SignedRatio.Equiv (SignedRatio.add
      (SignedRatio.mul (⟨left, left + right, positive⟩ : QProb).toSignedRatio x)
      (SignedRatio.mul (⟨right, left + right, positive⟩ : QProb).toSignedRatio x)) x := by
  have normalized : QProb.Equiv (QProb.add ⟨left, left + right, positive⟩ ⟨right, left + right, positive⟩) QProb.one := by
    change (left * (left + right) + right * (left + right)) * 1 = 1 * ((left + right) * (left + right))
    rw [← Nat.add_mul, Nat.mul_one, Nat.one_mul]
  have sum := QProb.toSignedRatio_congr normalized
  rw [QProb.toSignedRatio_add, QProb.toSignedRatio_one] at sum
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm (SignedRatio.add_mul _ _ x))
    (SignedRatio.equiv_trans (SignedRatio.mul_congr sum (SignedRatio.equiv_refl _)) (SignedRatio.one_mul x))

/-- Closed rational expectation intervals, including exact equalities, are
preserved by mixtures. Responses may be signed, and no row independence is
required, so redundant constraints need no preprocessing. -/
theorem MomentInterval.LawHolds_mixture [DecidableEq A] (constraint : MomentInterval A) (μ ν : Distro A)
    (grid : EntropyGrid A)
    (firstSupport : μ.AlmostSurely (fun value => value ∈ grid.cells))
    (secondSupport : ν.AlmostSurely (fun value => value ∈ grid.cells))
    (first : constraint.LawHolds μ) (second : constraint.LawHolds ν)
    (left right : Nat) (positive : 0 < left + right) : constraint.LawHolds (μ.mixture ν left right positive) := by
  have mean := μ.rationalExpectation_mixture_grid ν grid firstSupport secondSupport left right positive
    (fun value => ⟨constraint.response value, 1, Nat.zero_lt_one⟩)
  have lower := SignedRatio.add_le_add
    (SignedRatio.mul_le_mul_nonnegative (QProb.toSignedRatio_nonnegative (⟨left, left + right, positive⟩ : QProb)) first.1)
    (SignedRatio.mul_le_mul_nonnegative (QProb.toSignedRatio_nonnegative (⟨right, left + right, positive⟩ : QProb)) second.1)
  have upper := SignedRatio.add_le_add
    (SignedRatio.mul_le_mul_nonnegative (QProb.toSignedRatio_nonnegative (⟨left, left + right, positive⟩ : QProb)) first.2)
    (SignedRatio.mul_le_mul_nonnegative (QProb.toSignedRatio_nonnegative (⟨right, left + right, positive⟩ : QProb)) second.2)
  exact ⟨(SignedRatio.le_congr (signed_constant left right positive constraint.lower) (SignedRatio.equiv_symm mean)).mp lower,
    (SignedRatio.le_congr (SignedRatio.equiv_symm mean) (signed_constant left right positive constraint.upper)).mp upper⟩

namespace PartialMomentProblem

/-- Entropy uses the original declared grid, including every forced-zero cell. -/
def entropyGrid (problem : PartialMomentProblem A) : EntropyGrid A := ⟨problem.cells, problem.distinct⟩

def Admissible (problem : PartialMomentProblem A) (μ : Distro A) : Prop :=
  μ.AlmostSurely (fun value => value ∈ problem.cells) ∧ ∀ constraint ∈ problem.intervals, constraint.LawHolds μ

theorem admissible_mixture [DecidableEq A] (problem : PartialMomentProblem A) (μ ν : Distro A)
    (first : problem.Admissible μ) (second : problem.Admissible ν)
    (left right : Nat) (positive : 0 < left + right) : problem.Admissible (μ.mixture ν left right positive) :=
  ⟨μ.mixture_support ν left right positive _ first.1 second.1, fun constraint member =>
    constraint.LawHolds_mixture μ ν problem.entropyGrid first.1 second.1 (first.2 constraint member) (second.2 constraint member) left right positive⟩

/-- If a rational constrained entropy maximum is attained, it is unique as
a law, even with forced zeros, interval rows and redundant constraints. -/
theorem entropy_maximum_unique [DecidableEq A] (problem : PartialMomentProblem A)
    (μ ν : Distro A) (first : problem.Admissible μ) (second : problem.Admissible ν)
    (maxFirst : ∀ ρ (valid : problem.Admissible ρ),
      ExactLog.LE (ρ.entropy problem.entropyGrid valid.1) (μ.entropy problem.entropyGrid first.1))
    (maxSecond : ∀ ρ (valid : problem.Admissible ρ),
      ExactLog.LE (ρ.entropy problem.entropyGrid valid.1) (ν.entropy problem.entropyGrid second.1)) : μ.SameLaw ν :=
  Distro.entropy_maximum_unique problem.entropyGrid problem.Admissible (fun _ valid => valid.1)
    (fun μ ν first second => problem.admissible_mixture μ ν first second 1 1 (by decide)) μ ν first second maxFirst maxSecond

end PartialMomentProblem
end Thesis.Probability.Distros
