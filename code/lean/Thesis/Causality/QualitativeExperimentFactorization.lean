import Thesis.Causality.QualitativeExperimentRepresentation

namespace Thesis.Causality.CausalExperimentData
open Probability Probability.ClaytonWaddington
universe u v
variable {S : ObservedSignature.{u}} {P : FiniteLatentProjection S}

/-!
# Full interventional factorization is a consequence of the rules

The abstract interface does not assume a product formula. Effectiveness
gives a delta factor at a set variable; Parent sufficiency and Experimental
stability give the extracted draw-recipe factor at an unset variable. These
are local conclusions from qualitative equality and faithful calibration.

Their denominator-free history extension identity holds even for histories
of mass zero. Multiplying these identities along a complete compatible order
then proves the full-assignment factorization. Unrecorded nodes remain in
the product; deleting a hidden common cause would be a different claim.
-/

/-- The factor for an arbitrary next-node event. At a set variable its
drawing recipe is skipped; at an unset variable it is the extracted row. -/
def transitionWeight (data : CausalExperimentData S P) (completion : data.NullCompletion)
    (setting : HardIntervention S) (child) (reference : data.Assignment)
    (event : Event (data.Value child)) : QProb :=
  match data.forcedAt setting child with
  | some value => if event value then QProb.one else QProb.zero
  | none => (data.recipeWithCompletion completion child (data.parents child reference)).probVal event

/-- Successive cylinder extension, including null histories. There is no
division in the conclusion, and no support premise. -/
theorem history_extension (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (completion : data.NullCompletion) (setting) (child) (reference : data.Assignment)
    (event : Event (data.Value child)) :
    QProb.Equiv ((data.slice setting).probVal
      (fun sample => data.history child reference sample && data.nodeEvent child event sample))
      (QProb.mul ((data.slice setting).probVal (data.history child reference))
        (data.transitionWeight completion setting child reference event)) := by
  let record := FiniteProbRecord.ofUrn (data.slice setting)
  have transition : QProb.Equiv (record.probVal
      (fun sample => data.history child reference sample && data.nodeEvent child event sample))
      (QProb.mul (record.probVal (data.history child reference))
        (data.transitionWeight completion setting child reference event)) := by
    apply record.joint_equiv_mul_of_conditionals
    intro positive
    cases forced : data.forcedAt setting child with
    | some value =>
        simpa only [transitionWeight, forced] using
          data.conditional_of_forced scale rules setting child value forced
            (data.history child reference) event positive
    | none =>
        simpa only [transitionWeight, forced] using
          data.history_record_recipe scale rules completion setting child reference event forced positive
  exact QProb.equiv_trans (QProb.equiv_symm (FiniteProbRecord.ofUrn_agrees _ _))
    (QProb.equiv_trans transition
      (QProb.mul_congr (FiniteProbRecord.ofUrn_agrees _ _) (QProb.equiv_refl _)))

/-- The complete interventional joint is the product of extracted local
rows and forced-value delta factors. This is proved from the approved
qualitative rules, for every completion and every assignment, zeros included. -/
theorem full_factorization (data : CausalExperimentData S P)
    (scale : QualitativeUrnScale.{v}) (rules : QualitativeCausalRules data scale)
    (completion : data.NullCompletion) (setting) (reference : data.Assignment) :
    QProb.Equiv ((data.slice setting).probVal (FiniteProbRecord.singletonEvent reference))
      (data.order.nodes.foldl (fun product child => QProb.mul product
        (data.transitionWeight completion setting child reference
          (fun value => decide (value = reference child)))) QProb.one) := by
  let record := FiniteProbRecord.ofUrn (data.slice setting)
  let factor := fun child => data.transitionWeight completion setting child reference
    (fun value => decide (value = reference child))
  have product := OrderedHistory.singleton_factorization data.order.nodes data.order.complete
    record reference factor
  refine QProb.equiv_trans (QProb.equiv_symm (FiniteProbRecord.ofUrn_agrees _ _)) (product ?_)
  intro past child future same
  have earlier := data.order.earlier_eq_of_split past child future same
  have sameHistory : OrderedHistory.history past reference = data.history child reference := by
    unfold history
    rw [earlier]
  rw [sameHistory]
  refine QProb.equiv_trans (FiniteProbRecord.ofUrn_agrees _ _) ?_
  exact QProb.equiv_trans
    (data.history_extension scale rules completion setting child reference
      (fun value => decide (value = reference child)))
    (QProb.mul_congr (QProb.equiv_symm (FiniteProbRecord.ofUrn_agrees _ _)) (QProb.equiv_refl _))

end Thesis.Causality.CausalExperimentData
