import Thesis.Causality.CausalAbstraction
import Thesis.Probability.QProbOrder

namespace Thesis.Causality
open Probability

/-!
An event-wise remainder compares a pushed micro interventional law with a
macro law at an explicitly declared action, whether or not ω accepts that
pair. It is |p-q|, not a discrepancy between graph tags or a completed
conditional. Zero on one event is weaker than exactness; the equivalence
below quantifies over every event and every defined ω entry.
-/

namespace CausalRemainder

/-- Absolute rational difference, using witnessed natural subtraction.
No signed or approximate probability weights are needed. -/
def gap (p q : QProb) : QProb :=
  if order : QProb.LE q p then QProb.sub p q order
  else QProb.sub q p (Nat.le_of_lt (Nat.lt_of_not_ge order))

private theorem sub_zero_iff (p q : QProb) (order : QProb.LE q p) :
    QProb.Equiv (QProb.sub p q order) QProb.zero ↔ QProb.Equiv p q := by
  change (p.num * q.den - q.num * p.den) * 1 = 0 * (p.den * q.den) ↔
    p.num * q.den = q.num * p.den
  simp only [Nat.mul_one, Nat.zero_mul]
  constructor
  · intro zero
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero zero) order
  · intro equal
    rw [equal, Nat.sub_self]

theorem gap_zero_iff (p q : QProb) :
    QProb.Equiv (gap p q) QProb.zero ↔ QProb.Equiv p q := by
  unfold gap
  split
  · exact sub_zero_iff p q _
  · exact (sub_zero_iff q p _).trans ⟨QProb.equiv_symm, QProb.equiv_symm⟩

theorem gap_congr {p p' q q' : QProb} (first : QProb.Equiv p p')
    (second : QProb.Equiv q q') : QProb.Equiv (gap p q) (gap p' q') := by
  by_cases order : QProb.LE q p
  · have otherOrder := QProb.le_congr second first order
    simp only [gap, dif_pos order, dif_pos otherOrder]
    exact QProb.sub_congr first second order otherOrder
  · have otherOrder : ¬ QProb.LE q' p' := fun h => order (QProb.le_congr (QProb.equiv_symm second) (QProb.equiv_symm first) h)
    simp only [gap, dif_neg order, dif_neg otherOrder]
    exact QProb.sub_congr second first _ _

/-- Compare actual laws after aggregation. The macro action is declared
comparison data, not a replacement value for an undefined ω entry. -/
def eventRemainder (microModel : ExactModel micro) (macroModel : ExactModel coarse)
    (assignmentMap : micro.Assignment → coarse.Assignment)
    (intervention : HardIntervention micro) (action : HardIntervention coarse)
    (event : Event coarse.Assignment) : QProb :=
  gap (((microModel.interventionalDist intervention.value).map assignmentMap).probVal event)
    (macroModel.interventionalValue action.value event)

/-- A zero remainder is exactly agreement on this event, with the micro
probability expressed as a pullback along τ. It is not full-law exactness. -/
theorem eventRemainder_zero_iff (microModel : ExactModel micro) (macroModel : ExactModel coarse)
    (assignmentMap : micro.Assignment → coarse.Assignment)
    (intervention : HardIntervention micro) (action : HardIntervention coarse)
    (event : Event coarse.Assignment) :
    QProb.Equiv (eventRemainder microModel macroModel assignmentMap intervention action event) QProb.zero ↔
    QProb.Equiv (macroModel.interventionalValue action.value event)
      (microModel.interventionalValue intervention.value (fun state => event (assignmentMap state))) := by
  rw [eventRemainder, gap_zero_iff]
  have push := (microModel.interventionalDist intervention.value).map_probVal assignmentMap event
  constructor
  · intro equal
    exact QProb.equiv_trans (QProb.equiv_symm equal) push
  · intro equal
    exact QProb.equiv_trans push (QProb.equiv_symm equal)

end CausalRemainder

namespace CausalInterventionMap

/-- Defined or illegal comparisons use the same numerical remainder. -/
def remainder (mapping : CausalInterventionMap micro coarse)
    (intervention : HardIntervention micro) (action : HardIntervention coarse)
    (event : Event coarse.Assignment) : QProb :=
  CausalRemainder.eventRemainder mapping.microModel mapping.macroModel
    mapping.assignmentMap intervention action event

theorem exact_iff_remainder_zero (mapping : CausalInterventionMap micro coarse) :
    mapping.Exact ↔ ∀ intervention action, mapping.omega intervention = some action →
      ∀ event, QProb.Equiv (mapping.remainder intervention action event) QProb.zero := by
  constructor
  · intro exactness intervention action defined event
    exact (CausalRemainder.eventRemainder_zero_iff _ _ _ _ _ _).mpr
      (exactness intervention action defined event)
  · intro zero intervention action defined event
    exact (CausalRemainder.eventRemainder_zero_iff _ _ _ _ _ _).mp
      (zero intervention action defined event)

theorem comp_remainder_zero (first : CausalInterventionMap fine middle)
    (second : CausalInterventionMap middle coarse)
    (shared : first.macroModel = second.microModel)
    (firstExact : first.Exact) (secondExact : second.Exact)
    (intervention action) (defined : (first.comp second shared).omega intervention = some action)
    (event : Event coarse.Assignment) :
    QProb.Equiv ((first.comp second shared).remainder intervention action event) QProb.zero :=
  ((first.comp second shared).exact_iff_remainder_zero.mp
    (comp_exact first second shared firstExact secondExact)) intervention action defined event

/-- No accepted micro surgery can force this coarse coordinate, if every
image action leaves it unforced. This is an image obstruction, not a claim
that an arbitrary chosen lift covers every possible intervention semantics. -/
theorem no_representative_of_unforced_image (mapping : CausalInterventionMap micro coarse)
    (node : Fin coarse.count)
    (unforced : ∀ intervention action, mapping.omega intervention = some action → action.value node = none)
    (action : HardIntervention coarse) (value : coarse.Value node)
    (forced : action.value node = some value) :
    ∀ intervention, mapping.omega intervention ≠ some action := by
  intro intervention defined
  have absent := unforced intervention action defined
  rw [forced] at absent
  cases absent

end CausalInterventionMap
end Thesis.Causality
