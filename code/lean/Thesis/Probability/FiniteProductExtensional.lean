import Thesis.Probability.Construction

namespace Thesis
namespace Probability
namespace FiniteProduct

universe u
variable {n : Nat} {Value : Fin n → Type u}

/-!
# Rectangles determine an explicitly finite dependent-product law

Native source replacement first proves independence on rectangular events.
To preserve an arbitrary mixed query, those rectangles must determine the
whole law.  The bridge below uses the supplied complete coordinate lists and
decidable equalities to enumerate assignments and compare their singleton
masses.  It does not assume a uniqueness theorem for product measures or
select a representative assignment by choice.

Repeated coordinate labels are removed by the existing constructive list
deduplication.  Zero probabilities and an empty coordinate family are allowed.
-/

theorem rectangularEvent_assignment_singleton (decEq : (index : Fin n) → DecidableEq (Value index))
    (reference : Assignment n Value) :
    rectangularEvent n Value (fun index value => @decide (value = reference index) (decEq index _ _)) =
      @FiniteProbRecord.singletonEvent _ (assignmentDecidableEq n Value decEq) reference := by
  funext sample
  apply Bool.eq_iff_iff.mpr
  rw [rectangularEvent_eq_true_iff]
  simp only [FiniteProbRecord.singletonEvent, decide_eq_true_eq]
  constructor
  · intro equalCoordinates; exact funext equalCoordinates
  · intro equal; exact congrFun equal

theorem probVal_extensional_of_rectangles
    (left right : FiniteProbRecord (Assignment n Value))
    (values : (index : Fin n) → List (Value index))
    (complete : forall index value, value ∈ values index)
    (decEq : (index : Fin n) → DecidableEq (Value index))
    (rectangles : forall events, QProb.Equiv (left.probVal (rectangularEvent n Value events))
      (right.probVal (rectangularEvent n Value events)))
    (event : Event (Assignment n Value)) : QProb.Equiv (left.probVal event) (right.probVal event) := by
  letI : DecidableEq (Assignment n Value) := assignmentDecidableEq n Value decEq
  let labels := deduplicate (enumeration n Value values)
  apply FiniteProbRecord.probVal_extensional_of_singletons left right labels (deduplicate_nodup _)
    (fun assignment => (mem_deduplicate _ _).mpr (enumeration_complete n Value values complete assignment))
    (fun reference => ?_) event
  rw [← rectangularEvent_assignment_singleton decEq reference]
  exact rectangles _

end FiniteProduct
end Probability
end Thesis
