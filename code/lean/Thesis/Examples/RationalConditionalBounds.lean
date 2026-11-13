import Thesis.Probability.Distros.RationalConditionalBounds
import Thesis.Examples.RationalConditionalNormalization

namespace Thesis.Probability.Examples.RationalConditionalBounds

open Distros.RationalLinear Conditional
open RationalConditionalNormalization (denominator numerator weights half)

/-!
# Conditional intervals retain endpoints, interiors and null-evidence exclusion

On a three-cell simplex, condition on the first two cells and ask for the
first. Both endpoint values zero and one have explicit supported source
assignments. Therefore every sharp certificate, including the computed one,
has exactly those endpoints, and projection lifting constructs every rational
interior value. These proofs do not normalize a closed optimizer computation
or treat runtime output as mathematical evidence.
-/

def reference : UnitValueAssignment (simplexRows 3) denominator numerator where
  source := RationalConditionalNormalization.source
  nonnegative := by decide +kernel
  bounded := by decide +kernel

def endpointWeights (first : Bool) (i : Fin 3) : SignedRatio :=
  if i.val = (if first then 0 else 1) then SignedRatio.one else SignedRatio.zero

def endpoint (first : Bool) : UnitValueAssignment (simplexRows 3) denominator numerator where
  source := {
    values := endpointWeights first
    feasible := (satisfies_simplex_iff 3 _).mpr
      ⟨(by cases first <;> decide +kernel), (by cases first <;> decide +kernel)⟩
    positive := by cases first <;> decide +kernel
    bounded := by cases first <;> decide +kernel }
  nonnegative := by cases first <;> decide +kernel
  bounded := by cases first <;> decide +kernel

def computed : FractionalRange (simplexRows 3) denominator numerator := fractionalRange reference

theorem endpoint_values (certificate : FractionalRange (simplexRows 3) denominator numerator) :
    SignedRatio.Equiv certificate.lower.value SignedRatio.zero ∧ SignedRatio.Equiv certificate.upper.value SignedRatio.one := by
  have lowerValue : SignedRatio.Equiv (endpoint false).value SignedRatio.zero := by decide +kernel
  have upperValue : SignedRatio.Equiv (endpoint true).value SignedRatio.one := by decide +kernel
  exact ⟨SignedRatio.equiv_of_le_of_le
    ((SignedRatio.le_congr (SignedRatio.equiv_refl _) lowerValue).mp (certificate.bounds (endpoint false)).1)
    certificate.lower.nonnegative,
    SignedRatio.equiv_of_le_of_le certificate.upper.bounded
      ((SignedRatio.le_congr upperValue (SignedRatio.equiv_refl _)).mp (certificate.bounds (endpoint true)).2)⟩

theorem computed_endpoints :
    SignedRatio.Equiv computed.lower.value SignedRatio.zero ∧ SignedRatio.Equiv computed.upper.value SignedRatio.one :=
  endpoint_values computed

/-- An explicit original assignment, rather than only a proposition that
some law must exist, is returned for the requested interior value. -/
def computed_middle : {point : UnitValueAssignment (simplexRows 3) denominator numerator // SignedRatio.Equiv point.value half} :=
  computed.pointBetween half
    ((SignedRatio.le_congr computed_endpoints.1 (SignedRatio.equiv_refl _)).mpr (by decide +kernel))
    ((SignedRatio.le_congr (SignedRatio.equiv_refl _) computed_endpoints.2).mpr (by decide +kernel))

theorem null_evidence_excluded : ¬ Nonempty (ProgramAssignment (simplexRows 3) (fun _ => 0) numerator) := by
  rintro ⟨point⟩
  exact point.normalized.zero_denominator_impossible

end Thesis.Probability.Examples.RationalConditionalBounds
