import Thesis.Examples.CausalUrnGame
import Thesis.CausalTransport.QualitativeExperimentDoCalculus

namespace Thesis.Examples.QualitativeExperimentRepresentation
open Probability Causality Probability.ClaytonWaddington
open Thesis.Examples.CausalUrnGame

/-!
# Reconstruction at the support boundary

These are clients of the general characterization, not replacements for
its proofs. The supplied full graph contains the unrecorded source U.
Reconstruction keeps it even though the observer records only X and Y.

In the variable-recipe fixture X is observationally always false. The row
Y | X=true must nevertheless be recovered from do(X=true), where its true
probability is 2/3. In contrast U is unrecorded and always false, so X's
declared U=true row is never exercised by any admitted experiment. Two
different completions of that row must give the same experimental laws.
-/

def variableData := variableGame.experimentData (CausalOrder.canonical (projection true).hiddenDAG)
def variableRules (scale : QualitativeUrnScale) : QualitativeCausalRules variableData scale :=
  variableGame.qualitativeRules _ scale

def newParents : variableData.Parents (2 : Fin 3) :=
  variableData.parents (2 : Fin 3) (fun node => decide (node.val = 1))

theorem new_row_observationally_null :
    (variableData.slice (idle true)).probNum (variableData.parentEvent (2 : Fin 3) newParents) = 0 := by
  decide +kernel

theorem new_row_reached : variableData.RowSupported (2 : Fin 3) newParents (setX true) := by
  decide +kernel

/-- The finite search cannot classify this observationally null row as
unconstrained: its intervention context is explicitly supported. -/
theorem new_row_is_extracted : variableData.rowContext (2 : Fin 3) newParents ≠ none :=
  variableData.rowContext_exists _ _ (setX true) new_row_reached

theorem new_row_probability (completion : variableData.NullCompletion) :
    QProb.Equiv ((variableData.recipeWithCompletion completion (2 : Fin 3) newParents).probVal id)
      ⟨2, 3, by decide⟩ := by
  exact QProb.equiv_trans
    (variableData.recipe_agrees rationalScale (variableRules rationalScale) completion
      (setX true) (2 : Fin 3) newParents id new_row_reached.1 new_row_reached.2)
    (by decide +kernel)

def unreachableParents : variableData.Parents (1 : Fin 3) :=
  variableData.parents (1 : Fin 3) (fun _ => true)

/-- No setting of recorded X or Y can set the unrecorded U to true. The
unused X draw-row has no supported context, even across all experiments. -/
theorem unreachable_row : variableData.rowContext (1 : Fin 3) unreachableParents = none := by
  decide +kernel

def falseCompletion : variableData.NullCompletion := fun _ _ => certain false
def trueCompletion : variableData.NullCompletion := fun _ _ => certain true

theorem false_completion_row :
    QProb.Equiv ((variableData.recipeWithCompletion falseCompletion (1 : Fin 3) unreachableParents).probVal id)
      QProb.zero := by
  rw [CausalExperimentData.recipeWithCompletion, unreachable_row]
  decide +kernel

theorem true_completion_row :
    QProb.Equiv ((variableData.recipeWithCompletion trueCompletion (1 : Fin 3) unreachableParents).probVal id)
      QProb.one := by
  rw [CausalExperimentData.recipeWithCompletion, unreachable_row]
  decide +kernel

/-- The recipes differ, but every FULL event in every admitted experiment
has the same probability. This includes hidden coordinates and null events. -/
theorem different_completions_same_laws (setting) (event : Event variableData.Assignment) :
    QProb.Equiv (((variableData.realizeWithCompletion falseCompletion).fullUrn setting).probVal event)
      (((variableData.realizeWithCompletion trueCompletion).fullUrn setting).probVal event) :=
  variableData.completions_preserve_same_law rationalScale (variableRules rationalScale)
    falseCompletion trueCompletion setting event

def hiddenData := commonCauseGame.experimentData (CausalOrder.canonical (projection false).hiddenDAG)

/-- The entire recorded law is recovered in the hidden common-cause
example, including interventions. No independence of recorded X,Y is used. -/
theorem hidden_common_cause_roundTrip (setting) (event : Event (signature false).Assignment) :
    QProb.Equiv ((commonCauseGame.law setting).probVal event)
      ((hiddenData.realize.law setting).probVal event) := by
  have original := commonCauseGame.recordUrn_agrees setting event
  have reconstruction := hiddenData.realize_recorded_law rationalScale
    (commonCauseGame.qualitativeRules _ rationalScale) hiddenData.defaultCompletion setting event
  exact QProb.equiv_trans original
    (QProb.equiv_trans (QProb.equiv_symm (FiniteProbRecord.ofUrn_agrees _ _)) reconstruction)

def outcome : Event variableData.Assignment := variableData.nodeEvent (2 : Fin 3) id
def impossibleEvidence : Event variableData.Assignment := variableData.nodeEvent (1 : Fin 3) id

theorem unsupported_before : variableData.conditional rationalScale (idle true) outcome impossibleEvidence = none := by
  decide +kernel

theorem unsupported_after (completion : variableData.NullCompletion) :
    ((variableData.realizeWithCompletion completion).experimentData variableData.order).conditional
      rationalScale (idle true) outcome impossibleEvidence = none :=
  (variableData.realize_conditional_none_iff rationalScale (variableRules rationalScale)
    completion (idle true) outcome impossibleEvidence).mp unsupported_before

/-- Evidence is certain, while Y=true has probability zero. The recovered
conditional is therefore defined zero; it is distinct from the previous
undefined conditional even when recipe completions are arbitrary. -/
theorem supported_zero_after (completion : variableData.NullCompletion)
    (positive : 0 < ((variableData.realizeWithCompletion completion).fullUrn (idle true)).probNum topEvent) :
    QProb.Equiv
      (((variableData.realizeWithCompletion completion).fullUrn (idle true)).condVal outcome topEvent positive)
      QProb.zero := by
  have originalPositive : 0 < (variableData.slice (idle true)).probNum topEvent := by decide +kernel
  have originalZero : QProb.Equiv
      ((variableData.slice (idle true)).condVal outcome topEvent (by decide +kernel)) QProb.zero := by decide +kernel
  exact QProb.equiv_trans
    (QProb.equiv_symm (UrnProb.condVal_congr_of_probVal _ _
      (variableData.realizeWithCompletion_preserves_full rationalScale (variableRules rationalScale)
        completion (idle true)) outcome topEvent originalPositive positive))
    originalZero

/- A zero-weight label is deliberately retained in this ordinary record.
It need not satisfy a setting's equations; only positive mass matters. The
standard conversion to a uniform urn drops its zero sampling multiplicity,
and the characterization must preserve the resulting law. -/
def withZeroAtom (record : FiniteProbRecord Ω) (extra : Ω) : FiniteProbRecord Ω where
  atoms := (extra, 0) :: record.atoms
  den := record.den
  den_pos := record.den_pos
  total_mass := by simpa only [FiniteProbRecord.totalMass, Nat.zero_add] using record.total_mass

theorem withZeroAtom_agrees (record : FiniteProbRecord Ω) (extra : Ω) (event : Event Ω) :
    QProb.Equiv ((withZeroAtom record extra).probVal event) (record.probVal event) := by
  simp [withZeroAtom, FiniteProbRecord.probVal, FiniteProbRecord.eventMass, QProb.Equiv]

def zeroExtended (data : CausalExperimentData S P) (extra : data.Assignment) : CausalExperimentData S P :=
  { data with slice := fun setting => (withZeroAtom (FiniteProbRecord.ofUrn (data.slice setting)) extra).toUrn }

theorem zeroExtended_agrees (data : CausalExperimentData S P) (extra : data.Assignment) (setting) (event) :
    QProb.Equiv (((zeroExtended data extra).slice setting).probVal event) ((data.slice setting).probVal event) :=
  QProb.equiv_trans (QProb.equiv_symm ((withZeroAtom (FiniteProbRecord.ofUrn (data.slice setting)) extra).toUrn_agrees event))
    (QProb.equiv_trans (withZeroAtom_agrees _ extra event) (FiniteProbRecord.ofUrn_agrees _ event))

/-- Explicit zero atoms do not change whether the qualitative requirements
hold. The argument uses full event-law agreement, including support, rather
than requiring every listed label to obey a setting's forced values. -/
theorem zeroExtended_rules (data : CausalExperimentData S P) (extra : data.Assignment)
    (scale : QualitativeUrnScale) (rules : QualitativeCausalRules data scale) :
    QualitativeCausalRules (zeroExtended data extra) scale := by
  exact (zeroExtended data extra).rules_of_slice_agreement scale data.slice
    (zeroExtended_agrees data extra) rules

theorem zeroExtended_reconstruction (data : CausalExperimentData S P) (extra : data.Assignment)
    (scale : QualitativeUrnScale) (rules : QualitativeCausalRules data scale) (setting) (event : Event data.Assignment) :
    QProb.Equiv ((data.slice setting).probVal event)
      (((zeroExtended data extra).realize.fullUrn setting).probVal event) :=
  QProb.equiv_trans (QProb.equiv_symm (zeroExtended_agrees data extra setting event))
    ((zeroExtended data extra).realize_preserves_full scale (zeroExtended_rules data extra scale rules) setting event)

private def support (result : ProbabilityResult.Result) (defined : result.isSome = true) :
    ProbabilityResult.Supported result := by
  cases result with
  | none => cases defined
  | some value => exact ⟨value, .value (QProb.equiv_refl _)⟩

/-- A public Rule 2 application to the abstract interface. At this reference
Y=true has probability zero on both supported sides. The caller supplies
rules, separation and support, without supplying a representing game or SCM. -/
theorem abstract_rule2_supported_zero (scale : QualitativeUrnScale) :
    QualitativeDoCalculus.KernelPlausEqv scale
      (variableData.kernelPlaus scale
        (rule2Left NodeSet.empty (NodeSet.singleton (1 : Fin 2)) (NodeSet.singleton (0 : Fin 2)) NodeSet.empty)
        (state false true))
      (variableData.kernelPlaus scale
        (rule2Right NodeSet.empty (NodeSet.singleton (1 : Fin 2)) (NodeSet.singleton (0 : Fin 2)) NodeSet.empty)
        (state false true)) := by
  apply variableData.qualitative_rule2 scale (variableRules scale) NodeSet.empty
    (NodeSet.singleton (1 : Fin 2)) (NodeSet.singleton (0 : Fin 2)) NodeSet.empty (state false true)
  · exact FourWayDisjoint.emptyAction _ _ NodeSet.empty
      (NodeSet.disjoint_singletons_of_ne (S := signature true)
        (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by
          intro equal
          have impossible : (1 : Nat) = 0 := congrArg Fin.val equal
          cases impossible))
      (NodeSet.disjoint_empty_right _) (NodeSet.disjoint_empty_right _)
  · decide +kernel
  · exact support _ (by decide +kernel)
  · exact support _ (by decide +kernel)

end Thesis.Examples.QualitativeExperimentRepresentation
