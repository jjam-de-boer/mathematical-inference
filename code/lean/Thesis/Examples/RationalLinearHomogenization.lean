import Thesis.Probability.Distros.RationalLinearHomogenization

namespace Thesis.Probability.Examples.RationalLinearHomogenization

open Distros.RationalLinear

/-!
# Why conditional linearization must retain a positive scale

The impossible constant row `0 ≤ -1` becomes feasible at scale zero.
This tests the mathematical boundary of homogenization: forgetting the scale
condition can turn an infeasible original problem into an apparently feasible
one. Positive scaling instead has the proved forward and reverse meanings.
-/

def impossible : Inequality 1 := ⟨fun _ => 0, ⟨-1, 1, Nat.zero_lt_one⟩⟩

theorem zero_scale_is_spurious :
    impossible.homogenize.Holds (extend (fun _ => SignedRatio.zero) SignedRatio.zero) ∧
      ¬ impossible.Holds (fun _ => SignedRatio.zero) := by
  constructor <;> decide +kernel

/-- At positive scale, the same constant contradiction remains impossible.
The result ranges over all supplied rational coordinates and scales. -/
theorem positive_scale_keeps_contradiction (value scale : SignedRatio) (positive : 0 < scale.num) :
    ¬ impossible.homogenize.Holds (extend (fun _ => value) scale) := by
  rw [impossible.homogenize_unscaled_iff (fun _ => value) scale positive]
  intro valid
  have compared : SignedRatio.LE SignedRatio.zero impossible.bound :=
    (SignedRatio.le_congr (dot_zero 1 _) (SignedRatio.equiv_refl _)).mp valid
  exact (by decide +kernel : ¬ SignedRatio.LE SignedRatio.zero impossible.bound) compared

end Thesis.Probability.Examples.RationalLinearHomogenization
