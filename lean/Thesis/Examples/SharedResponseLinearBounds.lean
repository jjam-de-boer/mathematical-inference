import Thesis.CausalTransport.SharedResponseLinearBounds
import Thesis.Causality.BinaryBowModel

namespace Thesis.Causality.Examples.SharedResponseLinearBounds

open Probability
open Causality.SharedResponse

/-!
# Response-grid and original-model regressions

The three-valued fixture retains a null declared value, repeated occurrences,
zero weights and an unreduced denominator. A small closed test executes the
actual rational linear solver; no large multivariable catalogue is expanded.
Forcing the null value is still a legitimate hard intervention.

The bow fixture separately checks genuine ambiguity in the original native
class: two laws on the same full response grid agree observationally but
disagree after a null factual action is forced. Thus complete response-table
coverage is not confused with point identification. The two-value example
does not replace the three-valued declared-domain test.
-/

namespace Unary

def signature : ObservedSignature where
  count := 1
  Value := fun _ => Fin 3
  valueEnumeration := fun _ => List.finRange 3
  value_complete := fun _ value => List.mem_finRange value
  value_nodup := fun _ => finRange_nodup 3
  defaultValue := fun _ => 0
  valueDecidableEq := fun _ => inferInstance
  directed := fun _ _ => false
  directed_earlier := by intro _ _ impossible; cases impossible

def node : Fin signature.count := ⟨0, Nat.zero_lt_one⟩

def table (value : Fin 3) : Table signature := fun _ _ => value

def law : FiniteProbRecord (Table signature) :=
  ⟨[(table 0, 4), (table 1, 2), (table 0, 0), (table 2, 0)], 6, by decide, rfl⟩

def observed : FiniteProbRecord signature.Assignment :=
  law.map (eval signature (FiniteLatentSCM.noIntervention signature))

def one : Event signature.Assignment := fun values => decide (values node = (1 : Fin 3))
def two : Event signature.Assignment := fun values => decide (values node = (2 : Fin 3))
def forceTwo : HardIntervention signature := ⟨fun _ => some (2 : Fin 3)⟩

theorem exactly_three_response_atoms : (enumeration signature).length = 3 := by decide +kernel

theorem law_fits : Fits signature observed law := by
  intro event
  exact QProb.equiv_symm (law.map_probVal _ event)

def original : ProjectedHiddenDAGModel (graph signature) := asProjectedModel signature law

theorem original_fits : NativeFits signature observed original :=
  nativeFits_of_fits signature observed law law_fits

theorem observed_two_null : (observed.probVal two).num = 0 := by decide +kernel

theorem forced_two_certain :
    QProb.Equiv (original.model.interventionalValue forceTwo two) QProb.one :=
  QProb.equiv_trans (nativeModel_interventionalValue signature law forceTwo two) (by decide +kernel)

/-- Both endpoints are computed, not supplied by a pre-proved bound theorem. -/
theorem solver_factual_third :
    (match solveBounds signature observed (HardIntervention.empty signature) one with
    | .bounded sharp => decide (SignedRatio.Equiv sharp.lower ⟨1, 3, by decide⟩ ∧
        SignedRatio.Equiv sharp.upper ⟨1, 3, by decide⟩)
    | .incompatible _ => false) = true := by decide +kernel

theorem factual_point_identified : PointIdentified signature observed (HardIntervention.empty signature) one := by
  refine ⟨⟨original, original_fits⟩, ?_⟩
  intro left right leftFits rightFits
  exact QProb.equiv_trans (leftFits one) (QProb.equiv_symm (rightFits one))

end Unary

namespace Bow

open BinaryBow

def observed : FiniteProbRecord signature.Assignment := ⟨[(fun _ => false, 1)], 1, Nat.zero_lt_one, rfl⟩

def law (offFactual : Bool) : FiniteProbRecord (Table signature) :=
  lawOf signature (BinaryBow.model observed offFactual)

def original (offFactual : Bool) : ProjectedHiddenDAGModel (SharedResponse.graph signature) :=
  asProjectedModel signature (law offFactual)

theorem original_fits (offFactual : Bool) : NativeFits signature observed (original offFactual) := by
  apply nativeFits_of_fits
  intro event
  exact QProb.equiv_trans (lawOf_interventionalValue signature (BinaryBow.model observed offFactual)
    (FiniteLatentSCM.noIntervention signature) event) (observationalValue_preserved observed offFactual event)

theorem different_effects :
    ¬ QProb.Equiv ((original false).model.interventionalValue (intervention true) (fun values => values y))
      ((original true).model.interventionalValue (intervention true) (fun values => values y)) := by
  intro same
  have preserved (offFactual : Bool) :
      QProb.Equiv ((original offFactual).model.interventionalValue (intervention true) (fun values => values y))
        ((BinaryBow.model observed offFactual).interventionalValue (intervention true).value (fun values => values y)) :=
    QProb.equiv_trans (nativeModel_interventionalValue signature _ (intervention true) (fun values => values y))
      (lawOf_interventionalValue signature (BinaryBow.model observed offFactual) (intervention true).value (fun values => values y))
  have oldSame := QProb.equiv_trans (QProb.equiv_symm (preserved false))
    (QProb.equiv_trans same (preserved true))
  exact (by decide +kernel : ¬ QProb.Equiv
    ((BinaryBow.model observed false).interventionalValue (intervention true).value (fun values => values y))
    ((BinaryBow.model observed true).interventionalValue (intervention true).value (fun values => values y))) oldSame

theorem effect_not_point_identified :
    ¬ PointIdentified signature observed (intervention true) (fun values => values y) :=
  fun identified => different_effects (identified.2 _ _ (original_fits false) (original_fits true))

end Bow
end Thesis.Causality.Examples.SharedResponseLinearBounds
