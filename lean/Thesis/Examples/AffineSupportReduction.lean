import Thesis.Probability.AffineSupportReduction

namespace Thesis
namespace Probability
namespace Examples
namespace AffineSupportReduction

open Probability.AffineSupportReduction IntegerLinearAlgebra

/-!
# A real support reduction with exact moment and mass preservation

Three atoms carry integer moment labels zero, one and two.  Their positive
weights have mean one.  The constructed affine step removes an actual atom,
keeps all output weights natural, and scales the moment and total by its same
positive factor.  The fixture reduces the actual constructor; the reusable
fields certify arbitrary input sizes and integer moment matrices.

The zero-moment fixture checks the normalization-only case.  No observational
law or source independence theorem is asserted by these weight-level tests.
-/

def moments : Matrix 1 3 := fun _ column => (column.val : Int)
def weights : Weights 3 := fun _ => 1
def reduction := step moments weights (fun _ => by decide) (by decide)

theorem original_support : positiveCount weights = 3 := by decide +kernel
theorem strict_support_drop : positiveCount reduction.newWeights < positiveCount weights := reduction.positive_count_decreases
theorem dropped_old_positive : 0 < weights reduction.dropped := reduction.dropped_old_positive
theorem dropped_new_zero : reduction.newWeights reduction.dropped = 0 := reduction.dropped_zero
theorem factor_positive : 0 < reduction.factor := reduction.factor_positive

theorem reduced_mean_one :
    dot (moments 0) (fun index => (reduction.newWeights index : Int)) =
      dot (fun _ => 1) (fun index => (reduction.newWeights index : Int)) := by
  rw [reduction.moments_scaled 0, reduction.mass_scaled]
  rfl

theorem concrete_drop : positiveCount reduction.newWeights = 2 := by decide +kernel

def noMoments : Matrix 0 2 := fun row => Fin.elim0 row
def unequalWeights : Weights 2 := fun index => if index.val = 0 then 2 else 3
def normalizedOnly := step noMoments unequalWeights (by decide +kernel) (by decide)

theorem normalization_only_drops : positiveCount normalizedOnly.newWeights = 1 := by decide +kernel
theorem normalization_only_mass :
    dot (fun _ => 1) (fun index => (normalizedOnly.newWeights index : Int)) =
      (normalizedOnly.factor : Int) * dot (fun _ => 1) (fun index => (unequalWeights index : Int)) := normalizedOnly.mass_scaled

end AffineSupportReduction
end Examples
end Probability
end Thesis
