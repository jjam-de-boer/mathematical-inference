import Thesis.Causality.QualitativeExperiments
import Thesis.Causality.CausalUrnTickets

/-!
# Recipes from supported experimental contexts

Search every recorded hard setting for a supported parent configuration in
which the child is NOT set. The ordinary conditional urn, projected to the
child value, is a local recipe. Experimental stability makes its law
independent of which eligible setting the finite search encounters first.
Parent sufficiency will connect that row to complete earlier histories.

A row occurring only while the child is forced does not determine drawing
instructions. Such rows get an explicit completion. The public realization
constructs a one-cell completion itself: callers supply neither kernels nor
noise. An auxiliary completion parameter permits the general proof that all
these choices preserve exactly the same admitted experimental laws. No
conditional probability on null evidence is created by this construction.
-/

namespace Thesis.Causality
open Probability Probability.ClaytonWaddington
universe u v

namespace HardIntervention

/-- All public hard settings, including observationally null action values.
Unrecorded coordinates are not additional intervention targets. -/
def enumeration (S : ObservedSignature.{u}) : List (HardIntervention S) :=
  (FiniteProduct.enumeration S.count (fun node => Option (S.Value node))
    (fun node => none :: (S.valueEnumeration node).map some)).map (fun values => ⟨values⟩)

theorem enumeration_complete (S : ObservedSignature.{u}) (setting : HardIntervention S) :
    setting ∈ enumeration S := by
  apply List.mem_map.mpr
  refine ⟨setting.value, ?_, ?_⟩
  · apply FiniteProduct.enumeration_complete
    intro node value
    cases value with
    | none => exact List.mem_cons_self
    | some value =>
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨value, S.value_complete node value, rfl⟩)
  · cases setting
    rfl

end HardIntervention

namespace CausalExperimentData
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}



def RowSupported (data : CausalExperimentData S P) (child) (parents : data.Parents child)
    (setting : HardIntervention S) : Prop :=
  data.forcedAt setting child = none ∧ 0 < (data.slice setting).probNum (data.parentEvent child parents)

instance (data : CausalExperimentData S P) (child) (parents : data.Parents child) (setting) :
    Decidable (data.RowSupported child parents setting) := by
  unfold RowSupported
  infer_instance

private def findRow (data : CausalExperimentData S P) (child) (parents : data.Parents child) :
    List (HardIntervention S) → Option { setting : HardIntervention S // data.RowSupported child parents setting }
  | [] => none
  | setting :: rest => if supported : data.RowSupported child parents setting then
      some ⟨setting, supported⟩ else findRow data child parents rest

private theorem findRow_complete (data : CausalExperimentData S P) (child) (parents : data.Parents child)
    (settings : List (HardIntervention S)) (setting : HardIntervention S)
    (listed : setting ∈ settings) (supported : data.RowSupported child parents setting) :
    data.findRow child parents settings ≠ none := by
  induction settings with
  | nil => cases listed
  | cons first rest inductionHypothesis =>
      dsimp only [findRow]
      split
      · intro impossible
        cases impossible
      · rename_i notFirst
        rcases List.mem_cons.mp listed with same | inRest
        · subst setting
          exact False.elim (notFirst supported)
        · exact inductionHypothesis inRest

/-- A supported draw-context is computed as data, without choice from a
propositional existence proof. -/
def rowContext (data : CausalExperimentData S P) (child) (parents : data.Parents child) :
    Option { setting : HardIntervention S // data.RowSupported child parents setting } :=
  data.findRow child parents (HardIntervention.enumeration S)

theorem rowContext_exists (data : CausalExperimentData S P) (child) (parents : data.Parents child)
    (setting : HardIntervention S) (supported : data.RowSupported child parents setting) :
    data.rowContext child parents ≠ none :=
  data.findRow_complete child parents _ setting (HardIntervention.enumeration_complete S setting) supported

/-- Search fails exactly when the row has zero mass whenever this child is
drawn. The row may still occur while the child is forced, which skips its urn. -/
theorem rowContext_none_iff (data : CausalExperimentData S P) (child) (parents : data.Parents child) :
    data.rowContext child parents = none ↔ ∀ setting, data.forcedAt setting child = none →
      (data.slice setting).probNum (data.parentEvent child parents) = 0 := by
  constructor
  · intro absent setting unforced
    apply Nat.eq_zero_of_not_pos
    intro positive
    exact data.rowContext_exists child parents setting ⟨unforced, positive⟩ absent
  · intro nullRows
    cases selected : data.rowContext child parents with
    | none => rfl
    | some context =>
        have zero := nullRows context.val context.property.1
        have positive := context.property.2
        omega

/-- Consulted only on rows with no supported draw-context; this is not a
field or hypothesis of the abstract qualitative experimental system. -/
abbrev NullCompletion (data : CausalExperimentData S P) :=
  (child : Fin P.hiddenDAG.count) → data.Parents child → UrnProb (data.Value child)

def defaultCompletion (data : CausalExperimentData S P) : data.NullCompletion :=
  fun child _ => ⟨1, by decide, fun _ => data.defaultValue child⟩

def recipeWithCompletion (data : CausalExperimentData S P) (completion : data.NullCompletion)
    (child) (parents : data.Parents child) : UrnProb (data.Value child) :=
  match data.rowContext child parents with
  | none => completion child parents
  | some context =>
      ((data.slice context.val).conditionOn (data.parentEvent child parents) context.property.2).map
        (fun assignment => assignment child)

/-- Every eligible experiment agrees with the reconstructed row. The
completion is never inspected here, since a supported context rules out
search failure. Child events of probability zero remain included. -/
theorem recipe_agrees (data : CausalExperimentData S P) (scale : QualitativeUrnScale.{v})
    (rules : QualitativeCausalRules data scale) (completion : data.NullCompletion)
    (setting) (child) (parents : data.Parents child) (event : Event (data.Value child))
    (unforced : data.forcedAt setting child = none)
    (supported : 0 < (data.slice setting).probNum (data.parentEvent child parents)) :
    QProb.Equiv ((data.recipeWithCompletion completion child parents).probVal event)
      ((data.slice setting).condVal (data.nodeEvent child event) (data.parentEvent child parents) supported) := by
  cases selected : data.rowContext child parents with
  | none => exact False.elim (data.rowContext_exists child parents setting ⟨unforced, supported⟩ selected)
  | some context =>
      rw [recipeWithCompletion, selected]
      have stability := rules.experimentalStability context.val setting child parents event
        context.property.1 unforced context.property.2 supported
      have numerical := (data.conditionalPlaus_eqv_iff scale context.val setting _ _ _ _ _ _).mp stability
      refine QProb.equiv_trans
        (((data.slice context.val).conditionOn (data.parentEvent child parents) context.property.2).probVal_map
          (fun a : data.Assignment => a child) event) ?_
      exact QProb.equiv_trans
        ((data.slice context.val).conditionOn_probVal (data.parentEvent child parents)
          (data.nodeEvent child event) context.property.2) numerical

/-- Construct an operational game from the extracted rows. Existing game
machinery supplies its common tickets and fresh independent primitive draws. -/
def realizeWithCompletion (data : CausalExperimentData S P) (completion : data.NullCompletion) : CausalUrnGame S P where
  Value := data.Value
  values := data.values
  complete := data.complete
  valueEq := data.valueEq
  defaultValue := data.defaultValue
  recordedValue := data.recordedValue
  contents := data.recipeWithCompletion completion

/-- Public realization needs no caller-supplied local kernels or sources. -/
def realize (data : CausalExperimentData S P) : CausalUrnGame S P :=
  data.realizeWithCompletion data.defaultCompletion

theorem realizeWithCompletion_forcedAt (data : CausalExperimentData S P) (completion) (setting) (node) :
    (data.realizeWithCompletion completion).forcedAt setting node = data.forcedAt setting node := rfl

end CausalExperimentData
end Thesis.Causality
