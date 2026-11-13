import Thesis.CausalTransport.NativePathEncoding
import Thesis.Examples.NativeDemandSteps

namespace Thesis.Causality.Examples.NativeDemandPaths

open Probability NativeSupportProfiles NativeKernelInterfaceObstruction NativeDemandTypes
open Thesis.Causality.NativeDemandTyping Thesis.Causality.NativeDemandEncoding

/-!
# Empty sources, literal joins and supported finite path conversion

An empty path still checks its source, so a null conditional cannot acquire
a value by supplying no steps. A three-step detour has supported final
endpoints but an unsupported intermediate conditional; it remains rejected.
At a supported reference, the same detour is converted and checked normally.

Equal endpoint type tables do not permit a literal join between different
trees. Conversely, a reversed rule beneath a defined zero weight retains its
unsupported factor syntax and can participate in an actual two-step path.
One changing-weight path is also checked against the two conflicting profiles
together, preserving each profile's own factor demand without choosing two
different paths. Concrete input-support computations use kernel reduction;
the mixed-profile output is certified by the general conversion theorem.
No theorem relies on runtime output.
-/

def requested : Demand family := atReference (reference 2)

theorem empty_path_checks_its_source :
    (Path.encode? family (.nil (.kernel carrier)) requested).isSome = false ∧
      (Path.encode? family (.nil unitTerm) requested).map (fun path => path.check requested) = some true ∧
      (Path.encode? family (.nil (.kernel carrier)) (fun _ _ => false)).isSome = true := by decide +kernel

/-- Empty demand is coherent for an unused request but cannot stand for a
nonempty outer application, even when the erased expression has a value. -/
def vacuousEmpty := Path.nil (Term.encode family unitTerm (fun _ _ => false))

theorem empty_annotations_are_not_a_support_witness :
    checkDerivation family requested vacuousEmpty.erase.toDerivation = true ∧
      vacuousEmpty.check (fun _ _ => false) = true ∧
      vacuousEmpty.check requested = false := by decide +kernel

def detour := carrierDetour.linearize

theorem intermediate_support_is_retained :
    check family unitTerm requested = true ∧ check family productTerm requested = true ∧
      (Path.encode? family detour requested).isSome = false ∧
      (Path.encode? family detour (atReference (reference 0))).map
        (fun path => path.check (atReference (reference 0))) = some true := by decide +kernel

/-- The path index is the actual encoded tree. Even equal native types and
equivalent rational values cannot supply equality between kernel and product
constructors. No metadata-based join is available to `Path.cons`. -/
theorem equal_types_do_not_join :
    typeOf family unitTerm requested = typeOf family productTerm requested ∧
      Term.encode family unitTerm requested ≠ Term.encode family productTerm requested := by
  constructor
  · exact typeOf_eq_of_checked family requested expandUnit (by decide +kernel)
  · intro same
    have raw := congrArg Term.erase same
    rw [Term.erase_encode, Term.erase_encode] at raw
    cases raw

def nestedRoundTrip := DoCalculusRewritePath.cons NativeDemandSteps.nestedNullStep
  (.cons (.symm NativeDemandSteps.nestedNullStep) (.nil _))

def encodedNested := Path.encode family nestedRoundTrip requested (by decide +kernel)

theorem nested_zero_path_checked : encodedNested.check requested = true := by decide +kernel

theorem nested_path_is_recovered : encodedNested.eraseData = ⟨_, _, nestedRoundTrip⟩ :=
  Path.eraseData_encode family nestedRoundTrip requested (by decide +kernel)

def mixedRoundTrip := DoCalculusRewritePath.cons NativeDemandSteps.changingWeight
  (.cons (.symm NativeDemandSteps.changingWeight) (.nil _))
def mixedRequested : Demand conflicting := NativeDemandSteps.mixedRequested
def encodedMixed := Path.encode conflicting mixedRoundTrip mixedRequested (by decide +kernel)

/-- The weighted frame's masks agree propositionally as finite functions.
Its literal joins therefore carry function-equality transports that need not
normalize in `decide`. The quantified conversion theorem certifies this
output; the supplied native support proof is still computed in the kernel. -/
theorem one_path_checks_both_profiles : encodedMixed.check mixedRequested = true :=
  Path.encode_checked conflicting mixedRoundTrip mixedRequested (by decide +kernel)

/-- The output retains the same supplied two-step path, not one path for
the positive profile and a different path for the zero-weight profile. -/
theorem one_path_is_recovered : encodedMixed.eraseData = ⟨_, _, mixedRoundTrip⟩ :=
  Path.eraseData_encode conflicting mixedRoundTrip mixedRequested (by decide +kernel)

end Thesis.Causality.Examples.NativeDemandPaths
