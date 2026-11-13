import Thesis.Probability.Distros.ProjectionEquality

namespace Thesis.Probability.Distros

/-- The improvement from a finer finite observation is exactly the squared
distance between the two conditional means. Refinement is required only on
positive-weight occurrences; null outcomes and unsupported labels are retained. -/
theorem Distro.conditionalExpectation_refinement_gain_almostSurely (μ : Distro Ω)
    (fine : Ω → Fin n) (coarse : Ω → Fin m) (merge : Fin n → Fin m)
    (agrees : μ.AlmostSurely (fun x => coarse x = merge (fine x))) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalSquaredError f (μ.conditionalExpectation coarse f))
      (SignedRatio.add (μ.rationalSquaredError f (μ.conditionalExpectation fine f))
        (μ.rationalSquaredError (μ.conditionalExpectation fine f) (μ.conditionalExpectation coarse f))) := by
  let h := fun label => conditionalBlockMean
    (μ.record.atoms.filter (fun atom => decide (coarse atom.1 = merge label))) f
  have same : μ.AlmostSurely (fun x => SignedRatio.Equiv (h (fine x)) (μ.conditionalExpectation coarse f x)) := by
    intro atom member weight
    change SignedRatio.Equiv
      (conditionalBlockMean (μ.record.atoms.filter (fun other => decide (coarse other.1 = merge (fine atom.1)))) f)
      (conditionalBlockMean (μ.record.atoms.filter (fun other => decide (coarse other.1 = coarse atom.1))) f)
    rw [agrees atom member weight]
    exact SignedRatio.equiv_refl _
  have losses := μ.rationalSquaredError_congr_positive f f (fun x => h (fine x)) (μ.conditionalExpectation coarse f)
    (fun _ _ _ => SignedRatio.equiv_refl _) same
  have distances := μ.rationalSquaredError_congr_positive
    (μ.conditionalExpectation fine f) (μ.conditionalExpectation fine f)
    (fun x => h (fine x)) (μ.conditionalExpectation coarse f)
    (fun _ _ _ => SignedRatio.equiv_refl _) same
  exact SignedRatio.equiv_trans (SignedRatio.equiv_symm losses)
    (SignedRatio.equiv_trans (μ.conditionalExpectation_squaredError fine f h)
      (SignedRatio.add_congr (SignedRatio.equiv_refl _) distances))

/-- Refinement leaves the optimal error unchanged exactly when its two
conditional means agree almost surely, with rational equivalence throughout. -/
theorem Distro.conditionalExpectation_refinement_equal_iff_almostSurely (μ : Distro Ω)
    (fine : Ω → Fin n) (coarse : Ω → Fin m) (merge : Fin n → Fin m)
    (agrees : μ.AlmostSurely (fun x => coarse x = merge (fine x))) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalSquaredError f (μ.conditionalExpectation coarse f))
      (μ.rationalSquaredError f (μ.conditionalExpectation fine f)) ↔
    μ.AlmostSurely (fun x => SignedRatio.Equiv
      (μ.conditionalExpectation fine f x) (μ.conditionalExpectation coarse f x)) := by
  have split := μ.conditionalExpectation_refinement_gain_almostSurely fine coarse merge agrees f
  constructor
  · intro equal
    exact (μ.rationalSquaredError_zero_iff _ _).mp
      ((SignedRatio.add_equiv_left_iff _ _).mp (SignedRatio.equiv_trans (SignedRatio.equiv_symm split) equal))
  · intro equal
    exact SignedRatio.equiv_trans split ((SignedRatio.add_equiv_left_iff _ _).mpr
      ((μ.rationalSquaredError_zero_iff _ _).mpr equal))

theorem Distro.conditionalExpectation_refinement_gain (μ : Distro Ω)
    (fine : Ω → Fin n) (coarse : Ω → Fin m) (refinement : ObservableRefinement fine coarse) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalSquaredError f (μ.conditionalExpectation coarse f))
      (SignedRatio.add (μ.rationalSquaredError f (μ.conditionalExpectation fine f))
        (μ.rationalSquaredError (μ.conditionalExpectation fine f) (μ.conditionalExpectation coarse f))) :=
  μ.conditionalExpectation_refinement_gain_almostSurely fine coarse refinement.merge
    (fun atom _ _ => refinement.agrees atom.1) f

theorem Distro.conditionalExpectation_refinement_equal_iff (μ : Distro Ω)
    (fine : Ω → Fin n) (coarse : Ω → Fin m) (refinement : ObservableRefinement fine coarse) (f : Ω → SignedRatio) :
    SignedRatio.Equiv (μ.rationalSquaredError f (μ.conditionalExpectation coarse f))
      (μ.rationalSquaredError f (μ.conditionalExpectation fine f)) ↔
    μ.AlmostSurely (fun x => SignedRatio.Equiv
      (μ.conditionalExpectation fine f x) (μ.conditionalExpectation coarse f x)) :=
  μ.conditionalExpectation_refinement_equal_iff_almostSurely fine coarse refinement.merge
    (fun atom _ _ => refinement.agrees atom.1) f

end Thesis.Probability.Distros
