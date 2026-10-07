import Thesis.CausalTransport.HedgeConditionalRoot
import Thesis.Examples.HedgeReadoutPullback

namespace Thesis
namespace Causality
namespace Examples
namespace HedgeConditionalRootRegression

open Probability

/-!
# Multi-root conditional signal selection and finite-product boundaries

The probability fixture has genuinely different coordinate alphabets, of
sizes two and three.  Both laws have every cell positive and identical
one-coordinate marginals, but different dependence between the coordinates.
Their atom presentations also have different denominators.  A selector that
looked only at marginals, or silently matched denominators, would miss this
case.  The actual conditional search returns a separated cell instead.

The causal regression reuses the extracted two-root hedge from the merging
readout fixture.  Its root conditional and supported source-prior gap are
provided by the arbitrary-hedge theorem, with no hand-supplied conditional
gap or chosen root.  This regression does not claim that the selected root
has already been composed into an arbitrary conditional query's active path.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## Different coordinate alphabets and equal individual marginals -/

def Value (index : Fin 2) : Type := Fin (index.val + 2)

instance coordinateEq : (index : Fin 2) -> DecidableEq (Value index) := fun index => inferInstanceAs (DecidableEq (Fin (index.val + 2)))

private instance assignmentEq : DecidableEq (FiniteProduct.Assignment 2 Value) :=
  FiniteProduct.assignmentDecidableEq 2 Value coordinateEq

def values : List (FiniteProduct.Assignment 2 Value) :=
  deduplicate (FiniteProduct.enumeration 2 Value (fun index => List.finRange (index.val + 2)))

theorem values_complete (reference : FiniteProduct.Assignment 2 Value) : reference ∈ values := by
  rw [values, mem_deduplicate]
  exact FiniteProduct.enumeration_complete 2 Value (fun index => List.finRange (index.val + 2))
    (fun _ value => List.mem_finRange value) reference

theorem values_nodup : values.Nodup := deduplicate_nodup _

def firstIndex : Fin 2 := ⟨0, by decide⟩
def secondIndex : Fin 2 := ⟨1, by decide⟩

/-- A complete positive baseline with the balanced directions displayed
explicitly.  The left table has rows `3,2,1` and `1,2,3`; the right table has
weight two in every cell.  Both rows and all three columns therefore match. -/
def perturbation : FiniteRecordPerturbation (FiniteProduct.Assignment 2 Value) where
  values := values
  complete := values_complete
  anchor := fun _ => ⟨0, by omega⟩
  baseline := 1
  baselinePositive := by decide
  increase := fun sample => if (sample firstIndex).val = 0 then 2 - (sample secondIndex).val else (sample secondIndex).val
  decrease := fun _ => 1
  massBalanced := by decide +kernel

def left : FiniteProbRecord (FiniteProduct.Assignment 2 Value) := perturbation.leftRecord

/-- Repeat the right atoms literally.  This retains its normalized law but
doubles its denominator, so the comparison cannot depend on record equality
or on the two displayed conditioning masses being identical naturals. -/
def right : FiniteProbRecord (FiniteProduct.Assignment 2 Value) where
  atoms := perturbation.rightRecord.atoms ++ perturbation.rightRecord.atoms
  den := perturbation.rightRecord.den + perturbation.rightRecord.den
  den_pos := Nat.lt_of_lt_of_le perturbation.rightRecord.den_pos (Nat.le_add_right _ _)
  total_mass := by
    rw [FiniteProbRecord.totalMass_append, perturbation.rightRecord.total_mass]

theorem left_supported : FiniteProductConditionals.FullSupport left := perturbation.left_positive

theorem right_supported : FiniteProductConditionals.FullSupport right := by
  intro reference
  change 0 < FiniteProbRecord.eventMass (perturbation.rightRecord.atoms ++ perturbation.rightRecord.atoms)
    (FiniteProbRecord.singletonEvent reference)
  rw [FiniteProbRecord.eventMass_append]
  exact Nat.lt_of_lt_of_le (perturbation.right_positive reference) (Nat.le_add_right _ _)

theorem actual_denominators : left.den = 12 ∧ right.den = 24 := by decide +kernel

theorem individual_marginals_equal (index : Fin 2) (label : Value index) :
    QProb.Equiv (left.probVal (fun sample => decide (sample index = label)))
      (right.probVal (fun sample => decide (sample index = label))) := by
  rcases index with ⟨index, bound⟩
  match index with
  | 0 =>
      change Fin 2 at label
      rcases label with ⟨label, labelBound⟩
      match label with
      | 0 =>
          change QProb.Equiv (left.probVal (fun sample => decide (sample firstIndex = (0 : Fin 2))))
            (right.probVal (fun sample => decide (sample firstIndex = (0 : Fin 2))))
          decide +kernel
      | 1 =>
          change QProb.Equiv (left.probVal (fun sample => decide (sample firstIndex = (1 : Fin 2))))
            (right.probVal (fun sample => decide (sample firstIndex = (1 : Fin 2))))
          decide +kernel
      | _ + 2 => exact False.elim (by omega)
  | 1 =>
      change Fin 3 at label
      rcases label with ⟨label, labelBound⟩
      match label with
      | 0 =>
          change QProb.Equiv (left.probVal (fun sample => decide (sample secondIndex = (0 : Fin 3))))
            (right.probVal (fun sample => decide (sample secondIndex = (0 : Fin 3))))
          decide +kernel
      | 1 =>
          change QProb.Equiv (left.probVal (fun sample => decide (sample secondIndex = (1 : Fin 3))))
            (right.probVal (fun sample => decide (sample secondIndex = (1 : Fin 3))))
          decide +kernel
      | 2 =>
          change QProb.Equiv (left.probVal (fun sample => decide (sample secondIndex = (2 : Fin 3))))
            (right.probVal (fun sample => decide (sample secondIndex = (2 : Fin 3))))
          decide +kernel
      | _ + 3 => exact False.elim (by omega)
  | _ + 2 => exact False.elim (by omega)

def selectedEvent : Event (FiniteProduct.Assignment 2 Value) :=
  fun sample => decide ((sample firstIndex).val = 0 ∧ (sample secondIndex).val = 0)

theorem joint_event_gap : Not (QProb.Equiv (left.probVal selectedEvent) (right.probVal selectedEvent)) := by decide +kernel

/-- The general search finds a conditional signal despite the complete
absence of a one-coordinate marginal signal. -/
def selected := FiniteProductConditionals.disagreementOfEventGap left right left_supported right_supported
  values values_nodup values_complete selectedEvent joint_event_gap

theorem selected_conditional_gap : Not (QProb.Equiv
    (FiniteProductConditionals.conditionalAt left left_supported selected.pivot selected.reference)
    (FiniteProductConditionals.conditionalAt right right_supported selected.pivot selected.reference)) := selected.separated

/-- The search really runs in finite coordinate/reference order.  This cell's
conditional probabilities are `3/4` and `1/2`, not its equal marginals. -/
theorem selected_coordinates : selected.pivot = firstIndex ∧
    (selected.reference firstIndex).val = 0 ∧ (selected.reference secondIndex).val = 0 := by decide +kernel

theorem selected_conditional_values :
    QProb.Equiv (FiniteProductConditionals.conditionalAt left left_supported selected.pivot selected.reference)
      ⟨3, 4, by decide⟩ ∧
    QProb.Equiv (FiniteProductConditionals.conditionalAt right right_supported selected.pivot selected.reference)
      ⟨1, 2, by decide⟩ := by decide +kernel

/-! ## The zero-coordinate boundary -/

def emptyValue (_index : Fin 0) : Type := Bool

private instance emptyCoordinateEq : (index : Fin 0) -> DecidableEq (emptyValue index) := fun _ => inferInstanceAs (DecidableEq Bool)

def emptyAssignment : FiniteProduct.Assignment 0 emptyValue := fun index => Fin.elim0 index

def emptyLaw : FiniteProbRecord (FiniteProduct.Assignment 0 emptyValue) where
  atoms := [(emptyAssignment, 2)]
  den := 2
  den_pos := by decide
  total_mass := rfl

theorem empty_supported : FiniteProductConditionals.FullSupport emptyLaw := by
  intro reference
  have same : reference = emptyAssignment := by funext index; exact Fin.elim0 index
  subst reference
  decide +kernel

/-- With no coordinate to scan the search returns none; normalization, not
a fabricated pivot, accounts for uniqueness of this one-cell space. -/
theorem empty_search : FiniteProductConditionals.disagreement? emptyLaw emptyLaw empty_supported empty_supported
    [emptyAssignment] = none := rfl

/-! ## Actual positive SCM priors for an extracted multi-root hedge -/

noncomputable def causalWitness := HedgeMergedReadout.extraction.witness.conditionedRoot HedgeMergedReadout.rich

theorem selected_actual_root : HedgeMergedReadout.rootMask causalWitness.root = true := by
  exact (congrFun HedgeMergedReadout.extracted_roots causalWitness.root).symm.trans causalWitness.root_selected

theorem original_action_values : forall node, HedgeMergedReadout.query.action node = true ->
    causalWitness.reference node = HedgeMergedReadout.rich.second node := causalWitness.action_values

theorem selected_label_readout_gap : Not (QProb.Equiv
    (((HedgeMergedReadout.extraction.witness.largeCarrierDefectParityModel HedgeMergedReadout.rich).prior.conditionOn
      (causalWitness.sourceContext (HedgeMergedReadout.extraction.witness.largeCarrierDefectParityModel HedgeMergedReadout.rich))
      causalWitness.left_source_supported).probVal (fun unit => hedgeIsSecond causalWitness.readoutValues causalWitness.root
        ((HedgeMergedReadout.extraction.witness.largeCarrierDefectParityModel HedgeMergedReadout.rich).evalUnder
          (hedgeDoSecond HedgeMergedReadout.rich HedgeMergedReadout.query.action) unit causalWitness.root)))
    (((HedgeMergedReadout.extraction.witness.smallCarrierDefectParityModel HedgeMergedReadout.rich).prior.conditionOn
      (causalWitness.sourceContext (HedgeMergedReadout.extraction.witness.smallCarrierDefectParityModel HedgeMergedReadout.rich))
      causalWitness.right_source_supported).probVal (fun unit => hedgeIsSecond causalWitness.readoutValues causalWitness.root
        ((HedgeMergedReadout.extraction.witness.smallCarrierDefectParityModel HedgeMergedReadout.rich).evalUnder
          (hedgeDoSecond HedgeMergedReadout.rich HedgeMergedReadout.query.action) unit causalWitness.root)))) :=
  causalWitness.source_readout_separated

theorem original_intervention_retained :
    hedgeDoSecond causalWitness.readoutValues HedgeMergedReadout.query.action =
      hedgeDoSecond HedgeMergedReadout.rich HedgeMergedReadout.query.action := causalWitness.readoutValues_doSecond_eq

end HedgeConditionalRootRegression
end Examples
end Causality
end Thesis
